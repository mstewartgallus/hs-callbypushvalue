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

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code -> Data (U a)
  PairData :: Data a -> Data b -> Data (a :*: b)

data Code where
  GlobalCode :: Global a -> Stack a -> Code
  LetLabelCode :: Stack a -> Label a -> Code -> Code
  LetBeCode :: Data a -> Variable a -> Code -> Code
  ForceCode :: Data (U a) -> Stack a -> Code
  ThrowCode :: Stack (F a) -> Data a -> Code
  LambdaCode :: Stack (a :=> b) -> Variable a -> Label b -> Code -> Code

data Stack a where
  LabelStack :: Label a -> Stack a
  ToStack :: Variable a -> Code -> Stack (F a)
  ApplyStack :: Data a -> Stack b -> Stack (a :=> b)

simplifyExtract :: Cps t => DataRep Simplifier a -> DataRep t a
simplifyExtract term = abstract (simplify (build term))

data Simplifier

instance HasData Simplifier where
  newtype DataRep Simplifier a = DB (forall s. Unique.Stream s -> (SSet a, Data a))

instance HasCode Simplifier where
  newtype CodeRep Simplifier a = CB (forall s. Unique.Stream s -> Code)

instance HasStack Simplifier where
  newtype StackRep Simplifier a = SB (forall s. Unique.Stream s -> (SAlgebra a, Stack a))

instance HasLet Simplifier where
  letBe (DB x) f = CB $ \(Unique.Stream newId xs ys) ->
    let (xt, x') = x xs
        binder = Variable xt newId
     in case f (DB $ \_ -> (xt, VariableData binder)) of
          CB y ->
            let y' = y ys
             in LetBeCode x' binder y'

instance HasLetLabel Simplifier where
  letLabel (SB x) f = CB $ \(Unique.Stream newId xs ys) ->
    let (xt, x') = x xs
        binder = Label xt newId
     in case f (SB $ \_ -> (xt, LabelStack binder)) of
          CB y ->
            let y' = y ys
             in LetLabelCode x' binder y'

instance HasConstants Simplifier where
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantData k)

instance HasTuple Simplifier where
  pair (DB x) (DB y) = DB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (yt, y') = y xs
     in (SPair xt yt, PairData x' y')

instance HasThunk Simplifier where
  lambda (SB k) f = CB $ \(Unique.Stream aId (Unique.Stream bId _ ks) ys) ->
    let (a `SFn` b, k') = k ks
        binder = Variable a aId
        label = Label b bId
     in case f (DB $ \_ -> (a, VariableData binder)) (SB $ \_ -> (b, LabelStack label)) of
          CB y ->
            let y' = y ys
             in LambdaCode k' binder label y'

  thunk t f = DB $ \(Unique.Stream newId xs ys) ->
    let binder = Label t newId
     in case f (SB $ \_ -> (t, LabelStack binder)) of
          CB y ->
            let y' = y ys
             in (SU t, ThunkData binder y')
  force (DB k) (SB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ForceCode k' x'

  call g (SB k) = CB $ \s ->
    let (_, k') = k s
     in GlobalCode g k'

instance Cps Simplifier where
  letTo t f = SB $ \(Unique.Stream newId xs ys) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableData binder)) of
          CB y ->
            let y' = y ys
             in (SF t, ToStack binder y')

  throw (SB k) (DB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ThrowCode k' x'

  apply (DB x) (SB k) = SB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (kt, k') = k ks
     in (xt `SFn` kt, ApplyStack x' k')

build :: DataRep Simplifier a -> Data a
build (DB s) = snd (Unique.withStream s)

simplify :: Data a -> Data a
simplify (ThunkData binder body) = ThunkData binder (simpCode body)
simplify x = x

simpStack :: Stack a -> Stack a
simpStack (ToStack binder body) = ToStack binder (simpCode body)
simpStack (ApplyStack h t) = ApplyStack (simplify h) (simpStack t)
simpStack x = x

simpCode :: Code -> Code
simpCode code = case code of
  ThrowCode (ToStack binder body) value -> simpCode (LetBeCode value binder body)
  ForceCode (ThunkData label body) k -> simpCode (LetLabelCode k label body)
  ThrowCode k x -> ThrowCode (simpStack k) (simplify x)
  ForceCode f x -> ForceCode (simplify f) (simpStack x)
  LetLabelCode thing binder body -> LetLabelCode (simpStack thing) binder (simpCode body)
  LetBeCode thing binder body -> LetBeCode (simplify thing) binder (simpCode body)
  GlobalCode g k -> GlobalCode g (simpStack k)
  LambdaCode k binder label body -> LambdaCode (simpStack k) binder label (simpCode body)

abstract :: Cps t => Data a -> DataRep t a
abstract x = abstData x LabelMap.empty VarMap.empty

abstData :: Cps t => Data a -> LabelMap (StackRep t) -> VarMap (DataRep t) -> DataRep t a
abstData x = case x of
  ConstantData k -> \_ _ -> constant k
  VariableData v -> \_ env -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error "variable not found in environment"
  ThunkData label@(Label t _) body ->
    let body' = abstCode body
     in \lenv env ->
          thunk t $ \k ->
            body' (LabelMap.insert label k lenv) env

abstStack :: Cps t => Stack a -> LabelMap (StackRep t) -> VarMap (DataRep t) -> StackRep t a
abstStack stk = case stk of
  LabelStack v -> \lenv _ -> case LabelMap.lookup v lenv of
    Just x -> x
    Nothing -> error "label not found in environment"
  ToStack binder@(Variable t _) body ->
    let body' = abstCode body
     in \lenv env ->
          letTo t $ \value ->
            body' lenv (VarMap.insert binder value env)
  ApplyStack h t ->
    let h' = abstData h
        t' = abstStack t
     in \lenv env -> apply (h' lenv env) (t' lenv env)

abstCode :: Cps t => Code -> LabelMap (StackRep t) -> VarMap (DataRep t) -> CodeRep t Void
abstCode c = case c of
  GlobalCode g k ->
    let k' = abstStack k
     in \lenv env -> call g (k' lenv env)
  ThrowCode k x ->
    let value' = abstData x
        k' = abstStack k
     in \lenv env -> throw (k' lenv env) (value' lenv env)
  ForceCode k x ->
    let value' = abstStack x
        k' = abstData k
     in \lenv env -> force (k' lenv env) (value' lenv env)
  LetBeCode value binder body ->
    let value' = abstData value
        body' = abstCode body
     in \lenv env -> body' lenv (VarMap.insert binder (value' lenv env) env)
  LetLabelCode value binder body ->
    let value' = abstStack value
        body' = abstCode body
     in \lenv env -> body' (LabelMap.insert binder (value' lenv env) lenv) env
  LambdaCode k binder@(Variable t _) label@(Label a _) body ->
    let body' = abstCode body
        k' = abstStack k
     in \lenv env ->
          lambda
            (k' lenv env)
            ( \h n ->
                body' (LabelMap.insert label n lenv) (VarMap.insert binder h env)
            )
