{-# LANGUAGE GADTs, KindSignatures #-}
module VarMap where
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dynamic
import Data.Typeable
import Data.Text(Text)
import qualified Data.Text as Text

import Common

newtype VarMap (t :: * -> *) = VarMap (Map Text.Text Dynamic)

lookup :: Typeable t => Variable a -> VarMap t -> Maybe (t a)
lookup (Variable (Type _) name) (VarMap map) = case Map.lookup name map of
  Nothing -> Nothing
  Just x -> fromDynamic x

insert :: Typeable t => Variable a -> t a -> VarMap t -> VarMap t
insert (Variable (Type _) name) value (VarMap map) = VarMap (Map.insert name (toDyn value) map)
