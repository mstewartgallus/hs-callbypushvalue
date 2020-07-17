{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (abstractCode, build, Builder, Cbpv (..), Code, Data, simplify) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Explicit
import Global
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import qualified Pure
import Tuple
import Unique
import VarMap (VarMap)
import qualified VarMap as VarMap
import Variable

class (HasGlobals t, HasConstants t, HasLet t, Explicit t, Tuple t, Pure.Pure t) => Cbpv t where
  lambda :: SSet a -> (DataRep t a -> CodeRep t b) -> CodeRep t (a :=> b)
  thunk :: CodeRep t a -> DataRep t (U a)
  force :: DataRep t (U a) -> CodeRep t a

data Builder

build :: CodeRep Builder a -> Code a
build (CB s) = snd (Unique.withStream s)

instance HasCode Builder where
  newtype CodeRep Builder (a :: Algebra) = CB (forall s. Unique.Stream s -> (SAlgebra a, Code a))

instance HasData Builder where
  newtype DataRep Builder (a :: Set) = DB (forall s. Unique.Stream s -> (SSet a, Data a))

instance HasGlobals Builder where
  global g@(Global t _) = CB $ \_ -> (t, GlobalCode g)

instance HasConstants Builder where
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantData k)
  unit = DB $ \_ -> (SUnit, UnitData)

instance Pure.Pure Builder where
  pure (DB value) = CB $ \s ->
    let (t, value') = value s
     in (SF t, ReturnCode value')

instance HasLet Builder where
  letBe (DB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (tx, vx) = x xs
        binder = Variable tx newId
     in case f (DB $ \_ -> (tx, VariableData binder)) of
          CB b ->
            let (result, body) = b fs
             in (result, LetBeCode vx binder body)

instance Explicit Builder where
  letTo (CB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (SF tx, vx) = x xs
        binder = Variable tx newId
     in case f (DB $ \_ -> (tx, VariableData binder)) of
          CB b ->
            let (result, body) = b fs
             in (result, LetToCode vx binder body)

  apply (CB f) (DB x) = CB $ \(Unique.Stream _ fs xs) ->
    let (_ `SFn` b, vf) = f fs
        (_, vx) = x xs
     in (b, ApplyCode vf vx)

instance Tuple Builder where
  pair (DB x) (DB y) = DB $ \(Unique.Stream _ xs ys) ->
    let (xt, xv) = x xs
        (yt, yv) = y ys
     in (SPair xt yt, PairData xv yv)

instance Cbpv Builder where
  lambda t f = CB $ \(Unique.Stream newId xs fs) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableData binder)) of
          CB b ->
            let (result, body) = b fs
             in (t `SFn` result, LambdaCode binder body)
  force (DB thunk) = CB $ \s ->
    let (SU t, thunk') = thunk s
     in (t, ForceCode thunk')
  thunk (CB code) = DB $ \s ->
    let (t, code') = code s
     in (SU t, ThunkData code')

data Code a where
  LambdaCode :: Variable a -> Code b -> Code (a :=> b)
  ApplyCode :: Code (a :=> b) -> Data a -> Code b
  ForceCode :: Data (U a) -> Code a
  ReturnCode :: Data a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  UnpairCode :: Data (a :*: b) -> Variable a -> Variable b -> Code c -> Code c
  GlobalCode :: Global a -> Code a

data Data a where
  VariableData :: Variable a -> Data a
  ConstantData :: Constant a -> Data a
  UnitData :: Data Unit
  ThunkData :: Code a -> Data (U a)
  PairData :: Data a -> Data b -> Data (a :*: b)

{-
Simplify Call By Pair Data Inverses

So far we handle:

- force (thunk X) reduces to X
- thunk (force X) reduces to X
-}
simplify :: Code a -> Code a
simplify code = case code of
  LetToCode (ReturnCode value) binder body -> simplify (LetBeCode value binder body)
  ApplyCode (LambdaCode binder body) value -> simplify (LetBeCode value binder body)
  ForceCode (ThunkData x) -> simplify x
  ForceCode x -> ForceCode (simplifyData x)
  LambdaCode binder body -> LambdaCode binder (simplify body)
  ApplyCode f x -> ApplyCode (simplify f) (simplifyData x)
  ReturnCode value -> ReturnCode (simplifyData value)
  LetBeCode value binder body -> LetBeCode (simplifyData value) binder (simplify body)
  LetToCode action binder body -> LetToCode (simplify action) binder (simplify body)
  x -> x

simplifyData :: Data a -> Data a
simplifyData x = case x of
  ThunkData (ForceCode x) -> simplifyData x
  ThunkData x -> ThunkData (simplify x)
  x -> x

abstractCode :: Cbpv t => Code a -> CodeRep t a
abstractCode = abstractCode' VarMap.empty

abstractData :: Cbpv t => Data a -> DataRep t a
abstractData = abstractData' VarMap.empty

abstractCode' :: Cbpv t => VarMap (DataRep t) -> Code a -> CodeRep t a
abstractCode' env code = case code of
  LetBeCode term binder body -> letBe (abstractData' env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  LetToCode term binder body -> letTo (abstractCode' env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  ApplyCode f x ->
    let f' = abstractCode' env f
        x' = abstractData' env x
     in apply f' x'
  LambdaCode binder@(Variable t _) body -> lambda t $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  ForceCode th -> force (abstractData' env th)
  ReturnCode val -> Pure.pure (abstractData' env val)
  GlobalCode g -> global g

abstractData' :: Cbpv t => VarMap (DataRep t) -> Data x -> DataRep t x
abstractData' env x = case x of
  VariableData v@(Variable t u) -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error ("could not find var " ++ show u)
  ThunkData c -> thunk (abstractCode' env c)
  ConstantData k -> constant k
  UnitData -> unit
  PairData h t -> pair (abstractData' env h) (abstractData' env t)
