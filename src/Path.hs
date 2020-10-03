{-# LANGUAGE GADTs #-}

module Path (Path (..)) where

import Control.Category
import Prelude hiding (id, (.))

-- | The type of free categories, like lists for monoids but for categories
data Path cat a b where
  Id :: Path cat a a
  (:.:) :: cat b c -> Path cat a b -> Path cat a c

infixr 0 :.:

instance Category (Path cat) where
  id = Id
  Id . g = g
  (f :.: g) . h = f :.: (g . h)
