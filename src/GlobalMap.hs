{-# LANGUAGE GADTs, KindSignatures #-}
module GlobalMap where
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dynamic
import Data.Typeable
import Data.Text(Text)
import qualified Data.Text as Text

import Common

newtype GlobalMap (t :: * -> *) = GlobalMap (Map (Text, Text) Dynamic)

-- fixme... verify types ?
lookup :: Typeable t => Global a -> GlobalMap t -> Maybe (t a)
lookup (Global _ package name) (GlobalMap map) = case Map.lookup (package, name) map of
  Nothing -> Nothing
  Just x -> fromDynamic x

insert :: Typeable t => Global a -> t a -> GlobalMap t -> GlobalMap t
insert (Global _ package name) value (GlobalMap map) = GlobalMap (Map.insert (package, name) (toDyn value) map)

data Entry t where
  Entry :: Typeable t => Global a -> t a -> Entry t

fromList :: [Entry t] -> GlobalMap t
fromList entries = GlobalMap (Map.fromList (map entryToDynamic entries))

entryToDynamic :: Entry t -> ((Text, Text), Dynamic)
entryToDynamic (Entry (Global _ package name) value) = ((package, name), toDyn value)
