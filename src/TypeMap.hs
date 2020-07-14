{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module TypeMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Typeable
import TypeVariable
import Unique

newtype TypeMap t = TypeMap (Map Unique (Dyn t))

data Dyn t where
  Dyn :: Kind a -> t a -> Dyn t

empty :: TypeMap t
empty = TypeMap Map.empty

equalKind :: Kind a -> Kind b -> Maybe (a :~: b)
equalKind = undefined

lookup :: TypeVariable a -> TypeMap t -> Maybe (t a)
lookup (TypeVariable t name) (TypeMap m) = case Map.lookup name m of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalKind t t' of
    Just Refl -> Just x
    Nothing -> error "type variables do not match kind"

insert :: TypeVariable a -> t a -> TypeMap t -> TypeMap t
insert (TypeVariable t name) value (TypeMap m) = TypeMap (Map.insert name (Dyn t value) m)

delete :: TypeVariable a -> TypeMap t -> TypeMap t
delete (TypeVariable _ name) (TypeMap m) = TypeMap (Map.delete name m)
