{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Label (AnyLabel (..), Label (..)) where

import Common
import TextShow
import Type (Action)
import Unique (Unique)

data Label a = Label (SAlg a) Unique

data AnyLabel where
  AnyLabel :: Label a -> AnyLabel

instance Eq (Label a) where
  (Label _ x) == (Label _ y) = x == y

instance Eq AnyLabel where
  AnyLabel (Label _ x) == AnyLabel (Label _ y) = x == y

instance Ord (Label a) where
  compare (Label _ x) (Label _ y) = compare x y

instance TextShow (Label a) where
  showb (Label _ name) = fromString "l" <> showb name
