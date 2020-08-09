{-# LANGUAGE GADTs #-}

module Constant (Constant (..), typeOf) where

import Common
import Data.Word
import TextShow

data Constant a where
  U64Constant :: Word64 -> Constant U64

instance Eq (Constant a) where
  (U64Constant x) == (U64Constant y) = x == y

instance TextShow (Constant a) where
  showb (U64Constant n) = showb n

typeOf :: Constant a -> SSet a
typeOf (U64Constant _) = SU64
