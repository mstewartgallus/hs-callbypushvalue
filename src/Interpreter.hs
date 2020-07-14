{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (evaluate, Value (..), Kont (..), R (..)) where

import Common
import Constant
import Core
import Cps
import Data.Word
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

data family Value (a :: Set) :: *

data instance Value Unit = Coin

newtype instance Value U64 = I Word64

newtype instance Value (U a) = Thunk (Kont a -> R)

data instance Value (a :*: b) = Value a ::: Value b

newtype R = Behaviour (IO ())

data family Kont (a :: Alg) :: *

data instance Kont Void = Nil

newtype instance Kont (F a) = Returns (Value a -> R)

data instance Kont (a :=> b) = Apply (Value a) (Kont b)

data family X a

newtype instance X Code = C R

newtype instance X (Data a) = V (Value a)

newtype instance X (Stack a) = K (Kont a)

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

  unit = V Coin
  nil = K Nil

  global g (K k) = case GlobalMap.lookup g globals of
    Just (G x) -> C (x k)
    Nothing -> error "global not found in environment"
  constant (U64Constant x) = V (I x)

newtype G a = G (Kont a -> R)

globals :: GlobalMap G
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus strictPlusImpl,
      GlobalMap.Entry minus minusImpl
    ]

infixr 0 `Apply`

strictPlusImpl :: G (U64 :=> U64 :=> F U64)
strictPlusImpl = G $ \(I x `Apply` I y `Apply` Returns k) -> k (I (x + y))

minusImpl :: G (U (F U64) :=> U (F U64) :=> F U64)
minusImpl = G $ \(Thunk x `Apply` Thunk y `Apply` Returns k) ->
  x $ Returns $ \(I x') ->
    y $ Returns $ \(I y') ->
      k (I (x' - y'))
