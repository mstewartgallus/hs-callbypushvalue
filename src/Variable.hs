{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StrictData #-}

module Variable (AnyVariable (..), Variable (..)) where

import Common
import TextShow
import Unique (Unique)

data Variable a = Variable (SSet a) Unique

data AnyVariable = forall a. AnyVariable (Variable a)

instance Eq (Variable a) where
  (Variable _ x) == (Variable _ y) = x == y

instance Eq AnyVariable where
  AnyVariable (Variable _ x) == AnyVariable (Variable _ y) = x == y

instance Ord (Variable a) where
  compare (Variable _ x) (Variable _ y) = compare x y

instance TextShow (Variable a) where
  showb (Variable _ name) = fromString "v" <> showb name
