{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module HasFn (HasFn (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasFn t where
  lambda :: SSet a -> (Data t a -> Code t b) -> Code t (a ':=> b)
  apply :: Code t (a ':=> b) -> Data t a -> Code t b
