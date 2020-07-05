{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}

module VarMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Typeable
import Unique

newtype VarMap t = VarMap (Map Unique (Dyn t))

data Dyn t where
  Dyn :: Type a -> t a -> Dyn t

empty :: VarMap t
empty = VarMap Map.empty

lookup :: Variable a -> VarMap t -> Maybe (t a)
lookup (Variable t name) (VarMap map) = case Map.lookup name map of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalType t t' of
    Nothing -> Nothing
    Just Refl -> Just x

insert :: Variable a -> t a -> VarMap t -> VarMap t
insert (Variable t name) value (VarMap map) = VarMap (Map.insert name (Dyn t value) map)

delete :: Variable a -> VarMap t -> VarMap t
delete (Variable _ name) (VarMap map) = VarMap (Map.delete name map)
