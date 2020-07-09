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
import VarMap (VarMap)
import qualified VarMap
import Variable

evaluate :: Term a -> a
evaluate x = case abstract x VarMap.empty of
  Value value -> value

newtype X a = Value a

instance Cps X where
  letTo _ f = Value $ PopStack $ \x -> case f (Value x) of
    Value k -> k
  returns (Value x) (Value (PopStack k)) = Value (k x)
  letBe x f = f x
  pop (Value (PushStack x k)) f = f (Value x) (Value k)
  global g = case GlobalMap.lookup g globals of
    Just (G x) -> Value x
    Nothing -> error "global not found in environment"
  push (Value h) (Value t) = Value (PushStack h t)
  constant (IntegerConstant x) = Value x

newtype Y t a = Y (t a)

abstract :: Cps t => Term a -> VarMap (Y t) -> t a
abstract (ConstantTerm k) = \_ -> constant k
abstract (VariableTerm v) = \env -> case VarMap.lookup v env of
  Just (Y x) -> x
  Nothing -> error "variable not found in environment"
abstract (LetToTerm binder@(Variable t _) body) =
  let body' = abstract body
   in \env ->
        letTo t $ \value ->
          body' (VarMap.insert binder (Y value) env)
abstract (PushTerm h t) =
  let h' = abstract h
      t' = abstract t
   in \env -> push (h' env) (t' env)
abstract (GlobalTerm g) =
  let g' = global g
   in \_ -> g'
abstract (ReturnTerm value k) =
  let value' = abstract value
      k' = abstract k
   in \env -> returns (value' env) (k' env)
abstract (LetBeTerm value binder body) =
  let value' = abstract value
      body' = abstract body
   in \env -> body' (VarMap.insert binder (Y (value' env)) env)
abstract (PopTerm value h t body) =
  let value' = abstract value
      body' = abstract body
   in \env ->
        pop (value' env) $ \x y ->
          body' (VarMap.insert h (Y x) (VarMap.insert t (Y y) env))

data G a = G a

globals :: GlobalMap G
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus (G strictPlusImpl)
    ]

strictPlusImpl :: Stack (F (Stack (Integer :=> Integer :=> F Integer)))
strictPlusImpl = PopStack $ \(PushStack x (PushStack y (PopStack k))) -> k (x + y)
