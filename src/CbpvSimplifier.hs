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
simplifyExtract term = abstractC (simplify (build term))

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
Simplify Call By Pair D Inverses

So far we handle:

- force (thunk X) reduces to X
- thunk (force X) reduces to X
-}
simplify :: C a -> C a
simplify code = case code of
  LetToC (ReturnC value) binder body -> simplify (LetBeC value binder body)
  ApplyC (LambdaC binder body) value -> simplify (LetBeC value binder body)
  ForceC (ThunkD x) -> simplify x
  ForceC x -> ForceC (simplifyD x)
  LambdaC binder body -> LambdaC binder (simplify body)
  ApplyC f x -> ApplyC (simplify f) (simplifyD x)
  ReturnC value -> ReturnC (simplifyD value)
  LetBeC value binder body -> LetBeC (simplifyD value) binder (simplify body)
  LetToC action binder body -> LetToC (simplify action) binder (simplify body)
  x -> x

simplifyD :: D a -> D a
simplifyD x = case x of
  ThunkD (ForceC x) -> simplifyD x
  ThunkD x -> ThunkD (simplify x)
  x -> x

abstractC :: Cbpv t => C a -> Code t a
abstractC = abstractCode' VarMap.empty

abstractD :: Cbpv t => D a -> Data t a
abstractD = abstractData' VarMap.empty

abstractCode' :: Cbpv t => VarMap (Data t) -> C a -> Code t a
abstractCode' env code = case code of
  LetBeC term binder body -> letBe (abstractData' env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  LetToC term binder body -> letTo (abstractCode' env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  ApplyC f x ->
    let f' = abstractCode' env f
        x' = abstractData' env x
     in apply f' x'
  LambdaC binder@(Variable t _) body -> lambda t $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  ForceC th -> force (abstractData' env th)
  ReturnC val -> returns (abstractData' env val)
  GlobalC g -> global g

abstractData' :: Cbpv t => VarMap (Data t) -> D x -> Data t x
abstractData' env x = case x of
  VariableD v@(Variable t u) -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error ("could not find var " ++ show u)
  ThunkD c -> thunk (abstractCode' env c)
  ConstantD k -> constant k
  UnitD -> unit
  PairD h t -> pair (abstractData' env h) (abstractData' env t)
