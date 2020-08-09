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
import HasStack
import HasTuple

evaluate :: Data X a -> Value a
evaluate (V value) = value

data family Value (a :: Set) :: *

data instance Value Unit = Coin

newtype instance Value U64 = I Word64

newtype instance Value (U a) = Thunk (Kont a -> R)

data instance Value (a :*: b) = Value a ::: Value b

newtype R = Behaviour (IO ())

data family Kont (a :: Algebra) :: *

newtype instance Kont (F a) = Returns (Value a -> R)

data instance Kont (a :=> b) = Apply (Value a) (Kont b)

data X

instance HasData X where
  newtype Data X a = V {unV :: Value a}

instance HasCode X where
  newtype Code X a = C R

instance HasStack X where
  newtype Stack X a = K (Kont a)

instance HasConstants X where
  constant (U64Constant x) = V (I x)

instance HasTuple X where
  pair f g x = V (unV (f x) ::: unV (g x))
  first (V (x ::: _)) = V x
  second (V (_ ::: y)) = V y

instance HasLet X where
  whereIs = id

instance HasLabel X where
  label x f = f x

instance HasThunk X where
  thunk _ f = V $ Thunk $ \x -> case f (K x) of
    C k -> k
  force (V (Thunk f)) (K x) = C (f x)

instance HasReturn X where
  letTo _ f = K $ Returns $ \x -> case f (V x) of
    C k -> k
  returns (V x) (K (Returns k)) = C (k x)

instance HasFn X where
  V h <*> K t = K (Apply h t)
  lambda (K (Apply h t)) f = f (V h) (K t)

instance HasCall X where
  call g = case GlobalMap.lookup g globals of
    Just (G x) -> V $ Thunk x
    Nothing -> error "global not found in environment"

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
