{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasTuple (HasTuple (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasTuple t where
  pair :: Data t a -> Data t b -> Data t (a ':*: b)
  unpair :: Data t (a ':*: b) -> (Data t a -> Data t b -> Code t c) -> Code t c
  unpair = flip ofPair
  ofPair :: (Data t a -> Data t b -> Code t c) -> Data t (a ':*: b) -> Code t c
  ofPair = flip unpair
