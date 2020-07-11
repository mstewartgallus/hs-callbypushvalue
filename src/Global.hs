{-# LANGUAGE StrictData #-}

module Global (Global (..)) where

import Name (Name)
import TextShow
import Type (Action)

data Global a = Global (Action a) Name

instance Eq (Global a) where
  (Global _ n) == (Global _ n') = n == n && n == n'

instance TextShow (Global a) where
  showb (Global _ name) = showb name
