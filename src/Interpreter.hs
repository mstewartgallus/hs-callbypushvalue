{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (evaluate, X, Value (..), Kont (..), R (..)) where

import Common
import Constant
import Core
import Cps
import Data.Word
import GlobalMap (GlobalMap)
import qualified GlobalMap
import HasCode
import HasConstants
import HasData
import HasLet
import HasLetLabel
import HasStack
import HasThunk
import HasTuple

evaluate :: Data X a -> Value a
evaluate (V value) = value

data family Value (a :: Set) :: *

data instance Value 'Unit = Coin

newtype instance Value 'U64 = I Word64

newtype instance Value ('U a) = Thunk (Kont a -> R)

data instance Value (a ':*: b) = Value a ::: Value b

newtype R = Behaviour (IO ())

data family Kont (a :: Algebra) :: *

data instance Kont 'Void = Nil

newtype instance Kont ('F a) = Returns (Value a -> R)

data instance Kont (a ':=> b) = Apply (Value a) (Kont b)

data X

instance HasData X where
  newtype Data X a = V (Value a)

instance HasCode X where
  newtype Code X a = C R

instance HasStack X where
  newtype Stack X a = K (Kont a)

instance HasConstants X where
  constant (U64Constant x) = V (I x)
  unit = V Coin

instance HasTuple X where
  pair (V x) (V y) = V (x ::: y)
  unpair (V (x ::: y)) f = f (V x) (V y)

instance HasLet X where
  letBe x f = f x

instance HasLetLabel X where
  letLabel x f = f x

instance HasThunk X where
  lambda (K (Apply h t)) f = f (V h) (K t)
  thunk _ f = V $ Thunk $ \x -> case f (K x) of
    C k -> k
  force (V (Thunk f)) (K x) = C (f x)

  call g (K k) = case GlobalMap.lookup g globals of
    Just (G x) -> C (x k)
    Nothing -> error "global not found in environment"

instance Cps X where
  throw (K (Returns k)) (V x) = C (k x)

  letTo _ f = K $ Returns $ \x -> case f (V x) of
    C k -> k

  apply (V h) (K t) = K (Apply h t)

  nil = K Nil

newtype G a = G (Kont a -> R)

globals :: GlobalMap G
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus strictPlusImpl,
      GlobalMap.Entry minus minusImpl
    ]

infixr 0 `Apply`

strictPlusImpl :: G ('U64 ':=> 'U64 ':=> 'F 'U64)
strictPlusImpl = G $ \(I x `Apply` I y `Apply` Returns k) -> k (I (x + y))

minusImpl :: G ('U ('F 'U64) ':=> 'U ('F 'U64) ':=> 'F 'U64)
minusImpl = G $ \(Thunk x `Apply` Thunk y `Apply` Returns k) ->
  x $ Returns $ \(I x') ->
    y $ Returns $ \(I y') ->
      k (I (x' - y'))
