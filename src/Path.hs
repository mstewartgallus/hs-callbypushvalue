{-# LANGUAGE GADTs #-}

module Path (Path, make, flatten) where

import Control.Category
import Prelude hiding ((.), id)

data Path cat a b where
  Pure :: cat a b -> Path cat a b
  Id :: Path cat a a
  (:.:) :: Path cat b c -> Path cat a b -> Path cat a c

make :: c a b -> Path c a b
make = Pure

flatten :: Category c => Path c a b -> c a b
flatten (Pure x) = x
flatten Id = id
flatten (f :.: g) = flatten f . flatten g

instance Category (Path cat) where
  id = Id
  (.) = (:.:)
