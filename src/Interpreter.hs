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

newtype X a = Value a

instance Cps X where
  letTo _ f = Value $ PopStack $ \x -> case f (Value x) of
    Value k -> k
  returns (Value x) (Value (PopStack k)) = Value (k x)
  letBe x f = f x
  pop (Value (PushStack x k)) f = f (Value x) (Value k)
  global g = case GlobalMap.lookup g globals of
    Just (Id x) -> Value x
    Nothing -> error "global not found in environment"
  push (Value h) (Value t) = Value (PushStack h t)
  constant (IntegerConstant x) = Value x

newtype Y t a = Y (t a)

newtype L t a = L (t (Stack a))

abstract :: Cps t => Term a -> LabelMap (L t) -> VarMap (Y t) -> t a
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
abstract (PushTerm h t) =
  let h' = abstract h
      t' = abstract t
   in \lenv env -> push (h' lenv env) (t' lenv env)
abstract (GlobalTerm g) =
  let g' = global g
   in \_ _ -> g'
abstract (ReturnTerm value k) =
  let value' = abstract value
      k' = abstract k
   in \lenv env -> returns (value' lenv env) (k' lenv env)
abstract (LetBeTerm value binder body) =
  let value' = abstract value
      body' = abstract body
   in \lenv env -> body' lenv (VarMap.insert binder (Y (value' lenv env)) env)
abstract (PopTerm value h t body) =
  let value' = abstract value
      body' = abstract body
   in \lenv env ->
        pop (value' lenv env) $ \x y ->
          body' (LabelMap.insert t (L y) lenv) (VarMap.insert h (Y x) env)

newtype Id a = Id a

globals :: GlobalMap Id
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus (Id strictPlusImpl)
    ]

strictPlusImpl :: Stack (F (Stack (Integer :=> Integer :=> F Integer)))
strictPlusImpl = PopStack $ \(PushStack x (PushStack y (PopStack k))) -> k (x + y)
