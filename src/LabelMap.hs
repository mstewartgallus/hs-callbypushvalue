{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}

module LabelMap where

import Common
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Typeable
import Label
import Unique

newtype LabelMap t = LabelMap (Map Unique (Dyn t))

data Dyn t = forall a. Dyn (SAlg a) (t a)

empty :: LabelMap t
empty = LabelMap Map.empty

lookup :: Label a -> LabelMap t -> Maybe (t a)
lookup (Label t name) (LabelMap m) = case Map.lookup name m of
  Nothing -> Nothing
  Just (Dyn t' x) -> case equalAlg t t' of
    Just Refl -> Just x
    Nothing -> error "labels not of the same type"

insert :: Label a -> t a -> LabelMap t -> LabelMap t
insert (Label t name) value (LabelMap m) = LabelMap (Map.insert name (Dyn t value) m)

delete :: Label a -> LabelMap t -> LabelMap t
delete (Label _ name) (LabelMap m) = LabelMap (Map.delete name m)
