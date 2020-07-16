{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StrictData #-}

module Label (AnyLabel (..), Label (..)) where

import Common
import TextShow
import Unique (Unique)

data Label a = Label (SAlg a) Unique

data AnyLabel = forall a. AnyLabel (Label a)

instance Eq (Label a) where
  (Label _ x) == (Label _ y) = x == y

instance Eq AnyLabel where
  AnyLabel (Label _ x) == AnyLabel (Label _ y) = x == y

instance Ord (Label a) where
  compare (Label _ x) (Label _ y) = compare x y

instance TextShow (Label a) where
  showb (Label _ name) = fromString "l" <> showb name
