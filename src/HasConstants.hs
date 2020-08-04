module HasConstants (HasConstants (..)) where

import Constant
import HasData

class HasData t => HasConstants t where
  constant :: Constant a -> Data t a
