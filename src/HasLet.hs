{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasLet (HasLet (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasLet t where
  letBe :: SetRep t a -> (SetRep t a -> AlgRep t b) -> AlgRep t b
