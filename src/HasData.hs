{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasData (HasData (..)) where

import Common
import Data.Kind

class HasData t where
  data Data t :: Set -> Type
  probeData :: SSet a -> Data t a
