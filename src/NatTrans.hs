{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module NatTrans ((:~>) (..), (|*|), (#)) where

import Control.Category
import Prelude hiding ((.), id)

newtype f :~> g = NatTrans (forall x. f x -> g x)

(#) :: f :~> g -> f a -> g a
(#) (NatTrans f) = f

instance Category ((:~>)) where
  id = NatTrans id
  (NatTrans f) . (NatTrans g) = NatTrans (f . g)

newtype (:.:) f g x = Compose (f (g x))

(|*|) :: (Functor k) => f :~> g -> j :~> k -> (j :.: f) :~> (k :.: g)
NatTrans f |*| NatTrans g = NatTrans (\(Compose x) -> Compose (fmap f (g x)))
