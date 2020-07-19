{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasConstants (HasConstants (..)) where

import Common
import Constant
import HasData

class HasData t => HasConstants t where
  constant :: Constant a -> Data t a

  unit :: Data t Unit
