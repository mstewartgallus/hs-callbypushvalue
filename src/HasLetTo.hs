{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasLetTo (HasLetTo (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasLetTo t where
  letTo :: CodeRep t (F a) -> (DataRep t a -> CodeRep t b) -> CodeRep t b
  apply :: CodeRep t (a :=> b) -> DataRep t a -> CodeRep t b
