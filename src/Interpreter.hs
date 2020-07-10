{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (evaluate) where

import Common
import Constant
import Core
import Cps
import GlobalMap (GlobalMap)
import qualified GlobalMap
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import VarMap (VarMap)
import qualified VarMap
import Variable

evaluate :: Term a -> a
evaluate x = case abstract x LabelMap.empty VarMap.empty of
  Value value -> value

data X a where
  Value :: a -> X (Term a)
  Action :: R -> X Code
  K :: a -> X (Cps.Stack a)

instance Cps X where
  letTo _ f = K $ Returns $ \x -> case f (Value x) of
    Action k -> k
  throw (K (Returns k)) (Value x) = Action (k x)
  letBe x f = f x
  pop (K (x ::: k)) f = case f (K k) of
    K (Returns f') -> Action (f' x)
  global g = case GlobalMap.lookup g globals of
    Just (Id x) -> Value x
    Nothing -> error "global not found in environment"
  push (Value h) (K t) = K (h ::: t)
  constant (IntegerConstant x) = Value x
  thunk _ f = Value $ Thunk $ \x -> case f (K x) of
    Action k -> k
  lambda _ f = Value $ Thunk $ \(x ::: t) -> case f (Value x) of
    Value (Thunk k) -> k t
  force (Value (Thunk f)) (K x) = Action (f x)

newtype Y t a = Y (t (Term a))

newtype L t a = L (t (Cps.Stack a))

abstract :: Cps t => Term a -> LabelMap (L t) -> VarMap (Y t) -> t (Term a)
abstract (ConstantTerm k) = \_ _ -> constant k
abstract (VariableTerm v) = \_ env -> case VarMap.lookup v env of
  Just (Y x) -> x
  Nothing -> error "variable not found in environment"
abstract (ThunkTerm label@(Label t _) body) =
  let body' = abstCode body
   in \lenv env ->
        thunk t $ \k ->
          body' (LabelMap.insert label (L k) lenv) env
abstract (LambdaTerm label@(Variable t _) body) =
  let body' = abstract body
   in \lenv env ->
        lambda t $ \k ->
          body' lenv (VarMap.insert label (Y k) env)
abstract (GlobalTerm g) =
  let g' = global g
   in \_ _ -> g'

abstStack :: Cps t => Cps.Stack a -> LabelMap (L t) -> VarMap (Y t) -> t (Cps.Stack a)
abstStack (LabelStack v) = \lenv _ -> case LabelMap.lookup v lenv of
  Just (L x) -> x
  Nothing -> error "label not found in environment"
abstStack (ToStack binder@(Variable t _) body) =
  let body' = abstCode body
   in \lenv env ->
        letTo t $ \value ->
          body' lenv (VarMap.insert binder (Y value) env)
abstStack (PushStack h t) =
  let h' = abstract h
      t' = abstStack t
   in \lenv env -> push (h' lenv env) (t' lenv env)

abstCode :: Cps t => Code -> LabelMap (L t) -> VarMap (Y t) -> t Code
abstCode (ThrowCode k x) =
  let value' = abstract x
      k' = abstStack k
   in \lenv env -> throw (k' lenv env) (value' lenv env)
abstCode (ForceCode k x) =
  let value' = abstStack x
      k' = abstract k
   in \lenv env -> force (k' lenv env) (value' lenv env)
abstCode (LetBeCode value binder body) =
  let value' = abstract value
      body' = abstCode body
   in \lenv env -> body' lenv (VarMap.insert binder (Y (value' lenv env)) env)
abstCode (LetLabelCode value binder body) =
  let value' = abstStack value
      body' = abstCode body
   in \lenv env -> body' (LabelMap.insert binder (L (value' lenv env)) lenv) env
abstCode (PopCode value t body) =
  let value' = abstStack value
      body' = abstStack body
   in \lenv env ->
        pop (value' lenv env) $ \y ->
          body' (LabelMap.insert t (L y) lenv) env

newtype Id a = Id a

globals :: GlobalMap Id
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus (Id strictPlusImpl)
    ]

strictPlusImpl :: U (Integer :=> Integer :=> F Integer)
strictPlusImpl = Thunk $ \(x ::: y ::: Returns k) -> k (x + y)
