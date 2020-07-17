{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Tuple (Tuple (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => Tuple t where
  pair :: SetRep t a -> SetRep t b -> SetRep t (a :*: b)
  unpair :: SetRep t (a :*: b) -> (SetRep t a -> SetRep t b -> AlgRep t c) -> AlgRep t c
