{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Const (Const (..)) where

import Common
import Constant
import HasData

class HasData t => Const t where
  constant :: Constant a -> SetRep t a

  unit :: SetRep t Unit
