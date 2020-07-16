{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Explicit (Explicit (..)) where

import Basic
import Common
import Const

class (Basic t, Const t) => Explicit t where
  returns :: SetRep t a -> AlgRep t (F a)

  letTo :: AlgRep t (F a) -> (SetRep t a -> AlgRep t b) -> AlgRep t b
  letBe :: SetRep t a -> (SetRep t a -> AlgRep t b) -> AlgRep t b

  lambda :: SSet a -> (SetRep t a -> AlgRep t b) -> AlgRep t (a :=> b)
  apply :: AlgRep t (a :=> b) -> SetRep t a -> AlgRep t b
