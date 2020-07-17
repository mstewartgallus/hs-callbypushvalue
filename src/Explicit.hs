{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Explicit (Explicit (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => Explicit t where
  letTo :: AlgRep t (F a) -> (SetRep t a -> AlgRep t b) -> AlgRep t b
  lambda :: SSet a -> (SetRep t a -> AlgRep t b) -> AlgRep t (a :=> b)
  apply :: AlgRep t (a :=> b) -> SetRep t a -> AlgRep t b
