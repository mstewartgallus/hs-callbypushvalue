{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module Constant (Constant (..)) where

import TextShow

data Constant a where
  IntegerConstant :: Integer -> Constant Integer

instance Eq (Constant a) where
  (IntegerConstant x) == (IntegerConstant y) = x == y

instance TextShow (Constant a) where
  showb (IntegerConstant n) = showb n
