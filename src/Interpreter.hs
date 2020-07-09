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

evaluate :: Data a -> a
evaluate x = case abstractData x VarMap.empty of
  Value value -> value

data X t where
  Value :: a -> X (Data a)

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

newtype Y t a = Y (t (Data a))

abstractData :: Cps t => Data a -> VarMap (Y t) -> t (Data a)
abstractData (ConstantData k) = \_ -> constant k
abstractData (VariableData v) = \env -> case VarMap.lookup v env of
  Just (Y x) -> x
  Nothing -> error "variable not found in environment"
abstractData (LetToData binder@(Variable t _) body) =
  let body' = abstract body
   in \env ->
        letTo t $ \value ->
          body' (VarMap.insert binder (Y value) env)
abstractData (PushData h t) =
  let h' = abstractData h
      t' = abstractData t
   in \env -> push (h' env) (t' env)
abstractData (GlobalData g) =
  let g' = global g
   in \_ -> g'

abstract :: Cps t => Code -> VarMap (Y t) -> t Code
abstract (ReturnCode value k) =
  let value' = abstractData value
      k' = abstractData k
   in \env -> returns (value' env) (k' env)
abstract (LetBeCode value binder body) =
  let value' = abstractData value
      body' = abstract body
   in \env -> body' (VarMap.insert binder (Y (value' env)) env)
abstract (PopCode value h t body) =
  let value' = abstractData value
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
