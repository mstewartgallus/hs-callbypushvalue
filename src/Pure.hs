{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Pure (Pure (..)) where

import Basic
import Common
import Const

class (Const t, Basic t) => Pure t where
  pure :: SetRep t a -> AlgRep t (F a)
