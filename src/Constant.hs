{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module Constant (Constant (..), typeOf) where

import Core
import TextShow
import Type

data Constant a where
  IntegerConstant :: Integer -> Constant Integer

instance Eq (Constant a) where
  (IntegerConstant x) == (IntegerConstant y) = x == y

instance TextShow (Constant a) where
  showb (IntegerConstant n) = showb n

typeOf :: Constant a -> Type a
typeOf (IntegerConstant _) = IntType
