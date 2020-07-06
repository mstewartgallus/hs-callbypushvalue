{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module GlobalMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Typeable
import Global
import Name

data Dyn t where
  Dyn :: Type a -> t a -> Dyn t

newtype GlobalMap t = GlobalMap (Map Name (Dyn t))

-- fixme... verify types ?
lookup :: Global a -> GlobalMap t -> Maybe (t a)
lookup (Global t name) (GlobalMap map) = case Map.lookup name map of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalType t t' of
    Just Refl -> Just x

insert :: Global a -> t a -> GlobalMap t -> GlobalMap t
insert (Global t name) value (GlobalMap map) = GlobalMap (Map.insert name (Dyn t value) map)

data Entry t where
  Entry :: Global a -> t a -> Entry t

fromList :: [Entry t] -> GlobalMap t
fromList entries = GlobalMap (Map.fromList (map entryToDyn entries))

entryToDyn :: Entry t -> (Name, Dyn t)
entryToDyn (Entry (Global t name) value) = (name, Dyn t value)
