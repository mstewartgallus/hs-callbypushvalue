{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Explicit (Explicit (..)) where

import Basic
import Common
import Const
import qualified Pure

class (Basic t, Const t, Pure.Pure t) => Explicit t where
  letTo :: AlgRep t (F a) -> (SetRep t a -> AlgRep t b) -> AlgRep t b
  letBe :: SetRep t a -> (SetRep t a -> AlgRep t b) -> AlgRep t b

  lambda :: SSet a -> (SetRep t a -> AlgRep t b) -> AlgRep t (a :=> b)
  apply :: AlgRep t (a :=> b) -> SetRep t a -> AlgRep t b
