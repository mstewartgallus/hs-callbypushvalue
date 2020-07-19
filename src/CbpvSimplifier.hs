{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifier (Simplifier, simplifyExtract) where

import Cbpv
import Common
import Constant (Constant)
import qualified Constant
import Core
import Global
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasTuple
import Unique
import VarMap (VarMap)
import qualified VarMap as VarMap
import Variable

simplifyExtract :: Cbpv t => Code Simplifier a -> Code t a
simplifyExtract term = simplify VarMap.empty (build term)

build :: Code Simplifier a -> C a
build (CB s) = snd (Unique.withStream s)

data Simplifier

instance HasCode Simplifier where
  newtype Code Simplifier (a :: Algebra) = CB (forall s. Unique.Stream s -> (SAlgebra a, C a))

instance HasData Simplifier where
  newtype Data Simplifier (a :: Set) = DB (forall s. Unique.Stream s -> (SSet a, D a))

instance HasGlobals Simplifier where
  global g@(Global t _) = CB $ \_ -> (t, GlobalC g)

instance HasConstants Simplifier where
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantD k)
  unit = DB $ \_ -> (SUnit, UnitD)

instance HasReturn Simplifier where
  returns (DB value) = CB $ \s ->
    let (t, value') = value s
     in (SF t, ReturnC value')

instance HasLet Simplifier where
  letBe (DB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (tx, vx) = x xs
        binder = Variable tx newId
     in case f (DB $ \_ -> (tx, VariableD binder)) of
          CB b ->
            let (result, body) = b fs
             in (result, LetBeC vx binder body)

instance HasLetTo Simplifier where
  letTo (CB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (SF tx, vx) = x xs
        binder = Variable tx newId
     in case f (DB $ \_ -> (tx, VariableD binder)) of
          CB b ->
            let (result, body) = b fs
             in (result, LetToC vx binder body)

  apply (CB f) (DB x) = CB $ \(Unique.Stream _ fs xs) ->
    let (_ `SFn` b, vf) = f fs
        (_, vx) = x xs
     in (b, ApplyC vf vx)

instance HasTuple Simplifier where
  pair (DB x) (DB y) = DB $ \(Unique.Stream _ xs ys) ->
    let (xt, xv) = x xs
        (yt, yv) = y ys
     in (SPair xt yt, PairD xv yv)

instance Cbpv Simplifier where
  lambda t f = CB $ \(Unique.Stream newId xs fs) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableD binder)) of
          CB b ->
            let (result, body) = b fs
             in (t `SFn` result, LambdaC binder body)
  force (DB thunk) = CB $ \s ->
    let (SU t, thunk') = thunk s
     in (t, ForceC thunk')
  thunk (CB code) = DB $ \s ->
    let (t, code') = code s
     in (SU t, ThunkD code')

data C a where
  LambdaC :: Variable a -> C b -> C (a :=> b)
  ApplyC :: C (a :=> b) -> D a -> C b
  ForceC :: D (U a) -> C a
  ReturnC :: D a -> C (F a)
  LetToC :: C (F a) -> Variable a -> C b -> C b
  LetBeC :: D a -> Variable a -> C b -> C b
  UnpairC :: D (a :*: b) -> Variable a -> Variable b -> C c -> C c
  GlobalC :: Global a -> C a

data D a where
  VariableD :: Variable a -> D a
  ConstantD :: Constant a -> D a
  UnitD :: D Unit
  ThunkD :: C a -> D (U a)
  PairD :: D a -> D b -> D (a :*: b)

{-
Algebraicly Simplify Call By Push Value
-}
simplify :: Cbpv t => VarMap (Data t) -> C a -> Code t a
simplify env code = case code of
  LetToC (ReturnC value) binder body -> letBe (simplifyD env value) $ \x ->
    simplify (VarMap.insert binder x env) body
  ApplyC (LambdaC binder body) value -> letBe (simplifyD env value) $ \x ->
    simplify (VarMap.insert binder x env) body
  ForceC (ThunkD x) -> simplify env x
  ForceC x -> force (simplifyD env x)
  LambdaC binder@(Variable t _) body -> lambda t $ \x ->
    simplify (VarMap.insert binder x env) body
  ApplyC f x -> apply (simplify env f) (simplifyD env x)
  ReturnC value -> returns (simplifyD env value)
  LetBeC value binder body -> letBe (simplifyD env value) $ \x ->
    simplify (VarMap.insert binder x env) body
  LetToC action binder body -> letTo (simplify env action) $ \x ->
    simplify (VarMap.insert binder x env) body
  GlobalC g -> global g

simplifyD :: Cbpv t => VarMap (Data t) -> D a -> Data t a
simplifyD env x = case x of
  ThunkD (ForceC x) -> simplifyD env x
  ThunkD x -> thunk (simplify env x)
  VariableD x -> case VarMap.lookup x env of
    Just y -> y
  ConstantD k -> constant k
  UnitD -> unit
  PairD x y -> pair (simplifyD env x) (simplifyD env y)
