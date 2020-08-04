{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (Value (..), Kont (..), R (..)) where

import Common
import Constant
import Core
import Cps
import Data.Word
import GlobalMap (GlobalMap)
import qualified GlobalMap
import HasConstants
import HasLet
import HasTuple

data family Value (a :: Set) :: *

data instance Value 'Unit = Coin

newtype instance Value 'U64 = I Word64

newtype instance Value ('U a) = Thunk (Kont a -> R)

data instance Value (a ':*: b) = Value a ::: Value b

newtype R = Behaviour (IO ())

data family Kont (a :: Algebra) :: *

newtype instance Kont ('F a) = Returns (Value a -> R)

data instance Kont (a ':=> b) = Apply (Value a) (Kont b)

newtype Code (a :: Algebra) = C R

instance HasConstants Value where
  constant (U64Constant x) = I x

instance HasTuple Code Value where
  pair x y = x ::: y
  unpair (x ::: y) f = f x y

instance HasLet Code Value where
  whereIs = id

instance HasLabel Code Kont where
  label x f = f x

instance HasThunk Code Value Kont where
  thunk _ f = Thunk $ \x -> case f x of
    C k -> k
  force (Thunk f) x = C (f x)

instance HasReturn Code Value Kont where
  letTo _ f = Returns $ \x -> case f x of
    C k -> k
  returns x (Returns k) = C (k x)

instance HasFn Code Value Kont where
  h <*> t = Apply h t
  lambda (Apply h t) f = f h t

instance HasCall Value where
  call g = case GlobalMap.lookup g globals of
    Just (G x) -> Thunk x
    Nothing -> error "global not found in environment"

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
