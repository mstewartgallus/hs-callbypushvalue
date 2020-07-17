{-# LANGUAGE StrictData #-}

module Global (Global (..)) where

import Common
import Name (Name)
import TextShow

data Global a = Global (SAlgebra a) Name

instance Eq (Global a) where
  (Global _ n) == (Global _ n') = n == n && n == n'

instance TextShow (Global a) where
  showb (Global _ name) = showb name
