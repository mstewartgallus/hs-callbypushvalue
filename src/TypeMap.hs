{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module TypeMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Typeable
import Kind
import TypeVariable
import Unique

newtype TypeMap t = TypeMap (Map Unique (Dyn t))

data Dyn t where
  Dyn :: Kind a -> t a -> Dyn t

empty :: TypeMap t
empty = TypeMap Map.empty

lookup :: TypeVariable a -> TypeMap t -> Maybe (t a)
lookup (TypeVariable t name) (TypeMap map) = case Map.lookup name map of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalKind t t' of
    Just Refl -> Just x

insert :: TypeVariable a -> t a -> TypeMap t -> TypeMap t
insert (TypeVariable t name) value (TypeMap map) = TypeMap (Map.insert name (Dyn t value) map)

delete :: TypeVariable a -> TypeMap t -> TypeMap t
delete (TypeVariable _ name) (TypeMap map) = TypeMap (Map.delete name map)
