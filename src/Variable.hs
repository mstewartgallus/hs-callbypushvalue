{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Variable (AnyVariable (..), Variable (..)) where

import TextShow
import Type (Type)
import Unique (Unique)

data Variable a = Variable (Type a) Unique

data AnyVariable where
  AnyVariable :: Variable a -> AnyVariable

instance Eq (Variable a) where
  (Variable _ x) == (Variable _ y) = x == y

instance Eq AnyVariable where
  AnyVariable (Variable _ x) == AnyVariable (Variable _ y) = x == y

instance Ord (Variable a) where
  compare (Variable _ x) (Variable _ y) = compare x y

instance TextShow (Variable a) where
  showb (Variable _ name) = fromString "v" <> showb name
