{-# LANGUAGE StrictData #-}

module Global (Global (..)) where

import Common
import Data.Text (Text)
import TextShow

data Global a = Global (Type a) Text Text

instance Eq (Global a) where
  (Global _ a x) == (Global _ b y) = a == b && x == y

instance TextShow (Global a) where
  showb (Global _ package name) = fromText package <> fromString "/" <> fromText name
