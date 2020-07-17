{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Pure (Pure (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => Pure t where
  pure :: SetRep t a -> AlgRep t (F a)
