{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (evaluate, Value (..), Kont (..), R (..)) where

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

evaluate :: Data a -> Value a
evaluate x = case abstract x of
  V value -> value

data Value a where
  I :: Integer -> Value Integer
  Unit :: Value Unit
  Thunk :: (Kont a -> R) -> Value (U a)
  (:::) :: Value a -> Value b -> Value (a :*: b)

newtype R = Behaviour (IO ())

data Kont a where
  Nil :: Kont Void
  Returns :: (Value a -> R) -> Kont (F a)
  Apply :: Value a -> Kont b -> Kont (a :=> b)

data X a where
  C :: R -> X Code
  V :: Value a -> X (Data a)
  K :: Kont a -> X (Stack a)

instance Cps X where
  throw (K (Returns k)) (V x) = C (k x)
  force (V (Thunk f)) (K x) = C (f x)

  thunk _ f = V $ Thunk $ \x -> case f (K x) of
    C k -> k
  letTo _ f = K $ Returns $ \x -> case f (V x) of
    C k -> k

  lambda (K (Apply h t)) f = f (V h) (K t)
  apply (V h) (K t) = K (Apply h t)

  pop (V (h ::: t)) f = f (V h) (V t)
  push (V h) (V t) = V (h ::: t)

  unit = V Unit
  nil = K Nil

  global g (K k) = case GlobalMap.lookup g globals of
    Just (G x) -> C (x k)
    Nothing -> error "global not found in environment"
  constant (IntegerConstant x) = V (I x)

newtype G a = G (Kont a -> R)

globals :: GlobalMap G
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus strictPlusImpl,
      GlobalMap.Entry minus minusImpl
    ]

infixr 0 `Apply`

strictPlusImpl :: G (Integer :=> Integer :=> F Integer)
strictPlusImpl = G $ \(I x `Apply` I y `Apply` Returns k) -> k (I (x + y))

minusImpl :: G (U (F Integer) :=> U (F Integer) :=> F Integer)
minusImpl = G $ \(Thunk x `Apply` Thunk y `Apply` Returns k) ->
  x $ Returns $ \(I x') ->
    y $ Returns $ \(I y') ->
      k (I (x' - y'))
