{-# LANGUAGE StrictData #-}

module Global (Global (..)) where

import Name (Name)
import SystemF.Type
import TextShow

data Global a = Global (SType a) Name

instance Eq (Global a) where
  (Global _ n) == (Global _ n') = n == n && n == n'

instance TextShow (Global a) where
  showb (Global _ name) = showb name
