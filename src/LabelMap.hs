{-# LANGUAGE GADTs, KindSignatures #-}
module LabelMap where
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dynamic
import Data.Typeable
import Data.Text(Text)
import qualified Data.Text as Text

import Common

newtype LabelMap (t :: * -> *) = LabelMap (Map Text.Text Dynamic)

empty :: LabelMap t
empty = LabelMap Map.empty

lookup :: Typeable t => Label a -> LabelMap t -> Maybe (t a)
lookup (Label (Type _) name) (LabelMap map) = case Map.lookup name map of
  Nothing -> Nothing
  Just x -> fromDynamic x

insert :: Typeable t => Label a -> t a -> LabelMap t -> LabelMap t
insert (Label (Type _) name) value (LabelMap map) = LabelMap (Map.insert name (toDyn value) map)

delete :: Label a -> LabelMap t -> LabelMap t
delete (Label _ name) (LabelMap map) = LabelMap (Map.delete name map)
