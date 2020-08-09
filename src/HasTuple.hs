{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasTuple (HasTuple (..)) where

import Common
import HasData

class HasData t => HasTuple t where
  pair :: (Data t a -> Data t b) -> (Data t a -> Data t c) -> (Data t a -> Data t (b ':*: c))
  first :: Data t (a ':*: b) -> Data t a
  second :: Data t (a ':*: b) -> Data t b
