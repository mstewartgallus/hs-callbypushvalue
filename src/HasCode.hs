{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasCode (HasCode (..)) where

import Common
import Data.Kind

class HasCode t where
  data Code t :: Algebra -> Type
  probeCode :: SAlgebra a -> Code t a
