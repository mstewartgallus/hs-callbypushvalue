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

evaluate :: Data a -> a
evaluate x = case abstract x LabelMap.empty VarMap.empty of
  V value -> value

data X a where
  C :: R -> X Code
  V :: a -> X (Data a)
  K :: a -> X (Stack a)

instance Cps X where
  throw (K (Returns k)) (V x) = C (k x)
  force (V (Thunk f)) (K x) = C (f x)

  thunk _ f = V $ Thunk $ \x -> case f (K x) of
    C k -> k
  letTo _ f = K $ Returns $ \x -> case f (V x) of
    C k -> k

  lambda _ _ f = V $ Thunk $ \(x ::: t) -> case f (V x) (K t) of
    C act -> act
  push (V h) (K t) = K (h ::: t)

  nilStack = K Void
  global g (K k) = case GlobalMap.lookup g globals of
    Just (Thunk x) -> C (x k)
    Nothing -> error "global not found in environment"
  constant (IntegerConstant x) = V x

newtype Y t a = Y (t (Data a))

newtype L t a = L (t (Stack a))

abstract :: Cps t => Data a -> LabelMap (L t) -> VarMap (Y t) -> t (Data a)
abstract (ConstantData k) = \_ _ -> constant k
abstract (VariableData v) = \_ env -> case VarMap.lookup v env of
  Just (Y x) -> x
  Nothing -> error "variable not found in environment"
abstract (ThunkData label@(Label t _) body) =
  let body' = abstCode body
   in \lenv env ->
        thunk t $ \k ->
          body' (LabelMap.insert label (L k) lenv) env
abstract (LambdaData binder@(Variable t _) label@(Label a _) body) =
  let body' = abstCode body
   in \lenv env ->
        lambda t a $ \h k ->
          body' (LabelMap.insert label (L k) lenv) (VarMap.insert binder (Y h) env)

abstStack :: Cps t => Stack a -> LabelMap (L t) -> VarMap (Y t) -> t (Stack a)
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
abstCode (GlobalCode g k) =
  let k' = abstStack k
   in \lenv env -> global g (k' lenv env)
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

globals :: GlobalMap U
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus strictPlusImpl,
      GlobalMap.Entry minus minusImpl
    ]

strictPlusImpl :: U (Integer :=> Integer :=> F Integer)
strictPlusImpl = Thunk $ \(x ::: y ::: Returns k) -> k (x + y)

minusImpl :: U (U (F Integer) :=> U (F Integer) :=> F Integer)
minusImpl = Thunk $ \(Thunk x ::: Thunk y ::: Returns k) ->
  x $ Returns $ \x' ->
    y $ Returns $ \y' ->
      k (x' - y')
