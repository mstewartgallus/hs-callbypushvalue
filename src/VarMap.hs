{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module VarMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Typeable
import Unique
import Variable

newtype VarMap t = VarMap (Map Unique (Dyn t))

data Dyn t where
  Dyn :: SSet a -> t a -> Dyn t

empty :: VarMap t
empty = VarMap Map.empty

lookup :: Variable a -> VarMap t -> Maybe (t a)
lookup (Variable t name) (VarMap m) = case Map.lookup name m of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalSet t t' of
    Just Refl -> Just x
    Nothing -> error "variables not of the same type"

insert :: Variable a -> t a -> VarMap t -> VarMap t
insert (Variable t name) value (VarMap m) = VarMap (Map.insert name (Dyn t value) m)

delete :: Variable a -> VarMap t -> VarMap t
delete (Variable _ name) (VarMap m) = VarMap (Map.delete name m)
