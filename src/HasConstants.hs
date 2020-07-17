{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasConstants (HasConstants (..)) where

import Common
import Constant
import HasData

class HasData t => HasConstants t where
  constant :: Constant a -> SetRep t a

  unit :: SetRep t Unit
