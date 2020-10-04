{-# LANGUAGE GADTs #-}

module Constant (Constant (..), typeOf) where

import Data.Word
import SystemF.Type
import TextShow

data Constant a where
  U64Constant :: Word64 -> Constant U64

instance Eq (Constant a) where
  U64Constant x == U64Constant y = x == y

instance TextShow (Constant a) where
  showb (U64Constant n) = showb n

typeOf :: Constant a -> SType a
typeOf (U64Constant _) = SU64
