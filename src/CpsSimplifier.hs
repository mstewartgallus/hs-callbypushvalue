{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CpsSimplifier (Simplifier, simplifyExtract) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Cps
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasLetLabel
import HasStack
import HasThunk
import HasTuple
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

data D a where
  ConstantD :: Constant a -> D a
  VariableD :: Variable a -> D a
  ThunkD :: Label a -> C -> D (U a)
  PairD :: D a -> D b -> D (a :*: b)

data C where
  GlobalC :: Global a -> S a -> C
  LetLabelC :: S a -> Label a -> C -> C
  LetBeC :: D a -> Variable a -> C -> C
  ForceC :: D (U a) -> S a -> C
  ThrowC :: S (F a) -> D a -> C
  LambdaC :: S (a :=> b) -> Variable a -> Label b -> C -> C

data S a where
  LabelS :: Label a -> S a
  ToS :: Variable a -> C -> S (F a)
  ApplyS :: D a -> S b -> S (a :=> b)

simplifyExtract :: Cps t => Data Simplifier a -> Data t a
simplifyExtract term = abstract (simplify (build term))

data Simplifier

instance HasData Simplifier where
  newtype Data Simplifier a = DB (forall s. Unique.Stream s -> (SSet a, D a))

instance HasCode Simplifier where
  newtype Code Simplifier a = CB (forall s. Unique.Stream s -> C)

instance HasStack Simplifier where
  newtype Stack Simplifier a = SB (forall s. Unique.Stream s -> (SAlgebra a, S a))

instance HasLet Simplifier where
  letBe (DB x) f = CB $ \(Unique.Stream newId xs ys) ->
    let (xt, x') = x xs
        binder = Variable xt newId
     in case f (DB $ \_ -> (xt, VariableD binder)) of
          CB y ->
            let y' = y ys
             in LetBeC x' binder y'

instance HasLetLabel Simplifier where
  letLabel (SB x) f = CB $ \(Unique.Stream newId xs ys) ->
    let (xt, x') = x xs
        binder = Label xt newId
     in case f (SB $ \_ -> (xt, LabelS binder)) of
          CB y ->
            let y' = y ys
             in LetLabelC x' binder y'

instance HasConstants Simplifier where
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantD k)

instance HasTuple Simplifier where
  pair (DB x) (DB y) = DB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (yt, y') = y xs
     in (SPair xt yt, PairD x' y')

instance HasThunk Simplifier where
  lambda (SB k) f = CB $ \(Unique.Stream aId (Unique.Stream bId _ ks) ys) ->
    let (a `SFn` b, k') = k ks
        binder = Variable a aId
        label = Label b bId
     in case f (DB $ \_ -> (a, VariableD binder)) (SB $ \_ -> (b, LabelS label)) of
          CB y ->
            let y' = y ys
             in LambdaC k' binder label y'

  thunk t f = DB $ \(Unique.Stream newId xs ys) ->
    let binder = Label t newId
     in case f (SB $ \_ -> (t, LabelS binder)) of
          CB y ->
            let y' = y ys
             in (SU t, ThunkD binder y')
  force (DB k) (SB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ForceC k' x'

  call g (SB k) = CB $ \s ->
    let (_, k') = k s
     in GlobalC g k'

instance Cps Simplifier where
  letTo t f = SB $ \(Unique.Stream newId xs ys) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableD binder)) of
          CB y ->
            let y' = y ys
             in (SF t, ToS binder y')

  throw (SB k) (DB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ThrowC k' x'

  apply (DB x) (SB k) = SB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (kt, k') = k ks
     in (xt `SFn` kt, ApplyS x' k')

build :: Data Simplifier a -> D a
build (DB s) = snd (Unique.withStream s)

simplify :: D a -> D a
simplify (ThunkD binder body) = ThunkD binder (simpC body)
simplify x = x

simpS :: S a -> S a
simpS (ToS binder body) = ToS binder (simpC body)
simpS (ApplyS h t) = ApplyS (simplify h) (simpS t)
simpS x = x

simpC :: C -> C
simpC code = case code of
  ThrowC (ToS binder body) value -> simpC (LetBeC value binder body)
  ForceC (ThunkD label body) k -> simpC (LetLabelC k label body)
  ThrowC k x -> ThrowC (simpS k) (simplify x)
  ForceC f x -> ForceC (simplify f) (simpS x)
  LetLabelC thing binder body -> LetLabelC (simpS thing) binder (simpC body)
  LetBeC thing binder body -> LetBeC (simplify thing) binder (simpC body)
  GlobalC g k -> GlobalC g (simpS k)
  LambdaC k binder label body -> LambdaC (simpS k) binder label (simpC body)

abstract :: Cps t => D a -> Data t a
abstract x = abstD x LabelMap.empty VarMap.empty

abstD :: Cps t => D a -> LabelMap (Stack t) -> VarMap (Data t) -> Data t a
abstD x = case x of
  ConstantD k -> \_ _ -> constant k
  VariableD v -> \_ env -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error "variable not found in environment"
  ThunkD label@(Label t _) body ->
    let body' = abstC body
     in \lenv env ->
          thunk t $ \k ->
            body' (LabelMap.insert label k lenv) env

abstS :: Cps t => S a -> LabelMap (Stack t) -> VarMap (Data t) -> Stack t a
abstS stk = case stk of
  LabelS v -> \lenv _ -> case LabelMap.lookup v lenv of
    Just x -> x
    Nothing -> error "label not found in environment"
  ToS binder@(Variable t _) body ->
    let body' = abstC body
     in \lenv env ->
          letTo t $ \value ->
            body' lenv (VarMap.insert binder value env)
  ApplyS h t ->
    let h' = abstD h
        t' = abstS t
     in \lenv env -> apply (h' lenv env) (t' lenv env)

abstC :: Cps t => C -> LabelMap (Stack t) -> VarMap (Data t) -> Code t Void
abstC c = case c of
  GlobalC g k ->
    let k' = abstS k
     in \lenv env -> call g (k' lenv env)
  ThrowC k x ->
    let value' = abstD x
        k' = abstS k
     in \lenv env -> throw (k' lenv env) (value' lenv env)
  ForceC k x ->
    let value' = abstS x
        k' = abstD k
     in \lenv env -> force (k' lenv env) (value' lenv env)
  LetBeC value binder body ->
    let value' = abstD value
        body' = abstC body
     in \lenv env -> body' lenv (VarMap.insert binder (value' lenv env) env)
  LetLabelC value binder body ->
    let value' = abstS value
        body' = abstC body
     in \lenv env -> body' (LabelMap.insert binder (value' lenv env) lenv) env
  LambdaC k binder@(Variable t _) label@(Label a _) body ->
    let body' = abstC body
        k' = abstS k
     in \lenv env ->
          lambda
            (k' lenv env)
            ( \h n ->
                body' (LabelMap.insert label n lenv) (VarMap.insert binder h env)
            )
