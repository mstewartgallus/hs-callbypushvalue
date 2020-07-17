{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasLet (HasLet (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasLet t where
  letBe :: DataRep t a -> (DataRep t a -> CodeRep t b) -> CodeRep t b
