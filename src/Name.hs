{-# LANGUAGE StrictData #-}

module Name (Name (..)) where

import Data.Text (Text)
import TextShow

data Name = Name {package :: Text, name :: Text} deriving (Eq, Ord)

instance TextShow Name where
  showb x = fromText (package x) <> fromString "/" <> fromText (name x)
