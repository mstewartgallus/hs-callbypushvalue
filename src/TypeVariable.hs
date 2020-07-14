{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module TypeVariable (TypeVariable (..)) where

import Common
import TextShow
import Unique (Unique)

data TypeVariable a = TypeVariable (Kind a) Unique

instance Eq (TypeVariable a) where
  (TypeVariable _ x) == (TypeVariable _ y) = x == y

instance TextShow (TypeVariable a) where
  showb (TypeVariable _ name) = fromString "t" <> showb name
