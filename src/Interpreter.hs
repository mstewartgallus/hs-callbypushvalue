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

instance Cps X where
  letTo _ f = Value $ PopStack $ \x -> case f (Value x) of
    Value k -> k
  apply (Value (PopStack k)) (Value x) = Value (k x)
  letBe x f = f x
  pop (Value (PushStack x k)) f = case f (Value k) of
    Value (PopStack f') -> Value $ f' x
  global g = case GlobalMap.lookup g globals of
    Just (Id x) -> Value x
    Nothing -> error "global not found in environment"
  push (Value h) (Value t) = Value (PushStack h t)
  constant (IntegerConstant x) = Value x
  thunk _ f = Value $ Thunk $ \x -> case f (Value x) of
    Value k -> k
  force (Value (Thunk f)) (Value x) = Value (f x)

newtype Y t a = Y (t (Term a))

newtype L t a = L (t (Term (Stack a)))

abstract :: Cps t => Term a -> LabelMap (L t) -> VarMap (Y t) -> t (Term a)
abstract (ConstantTerm k) = \_ _ -> constant k
abstract (VariableTerm v) = \_ env -> case VarMap.lookup v env of
  Just (Y x) -> x
  Nothing -> error "variable not found in environment"
abstract (LabelTerm v) = \lenv _ -> case LabelMap.lookup v lenv of
  Just (L x) -> x
  Nothing -> error "label not found in environment"
abstract (LetToTerm binder@(Variable t _) body) =
  let body' = abstract body
   in \lenv env ->
        letTo t $ \value ->
          body' lenv (VarMap.insert binder (Y value) env)
abstract (ThunkTerm label@(Label t _) body) =
  let body' = abstract body
   in \lenv env ->
        thunk t $ \k ->
          body' (LabelMap.insert label (L k) lenv) env
abstract (PushTerm h t) =
  let h' = abstract h
      t' = abstract t
   in \lenv env -> push (h' lenv env) (t' lenv env)
abstract (GlobalTerm g) =
  let g' = global g
   in \_ _ -> g'
abstract (ApplyTerm k x) =
  let value' = abstract x
      k' = abstract k
   in \lenv env -> apply (k' lenv env) (value' lenv env)
abstract (ForceTerm k x) =
  let value' = abstract x
      k' = abstract k
   in \lenv env -> force (k' lenv env) (value' lenv env)
abstract (LetBeTerm value binder body) =
  let value' = abstract value
      body' = abstract body
   in \lenv env -> body' lenv (VarMap.insert binder (Y (value' lenv env)) env)
abstract (PopTerm value t body) =
  let value' = abstract value
      body' = abstract body
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
strictPlusImpl = Thunk $ \(PushStack x (PushStack y (PopStack k))) -> k (x + y)
