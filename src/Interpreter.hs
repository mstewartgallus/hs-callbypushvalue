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
evaluate x = case abstract x of
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
