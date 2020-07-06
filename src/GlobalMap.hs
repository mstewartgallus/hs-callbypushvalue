{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module GlobalMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Typeable

data Dyn t where
  Dyn :: Type a -> t a -> Dyn t

newtype GlobalMap t = GlobalMap (Map (Text, Text) (Dyn t))

-- fixme... verify types ?
lookup :: Global a -> GlobalMap t -> Maybe (t a)
lookup (Global t package name) (GlobalMap map) = case Map.lookup (package, name) map of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalType t t' of
    Just Refl -> Just x

insert :: Global a -> t a -> GlobalMap t -> GlobalMap t
insert (Global t package name) value (GlobalMap map) = GlobalMap (Map.insert (package, name) (Dyn t value) map)

data Entry t where
  Entry :: Global a -> t a -> Entry t

fromList :: [Entry t] -> GlobalMap t
fromList entries = GlobalMap (Map.fromList (map entryToDyn entries))

entryToDyn :: Entry t -> ((Text, Text), Dyn t)
entryToDyn (Entry (Global t package name) value) = ((package, name), Dyn t value)
