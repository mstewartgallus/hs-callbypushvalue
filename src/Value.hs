{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

module Value (Value (..), interpret) where

import Common
import HasData

newtype Value k a = Value (forall t. k t => DataRep t a)

interpret :: k t => Value k a -> DataRep t a
interpret (Value x) = x
