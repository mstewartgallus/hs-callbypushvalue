{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasCode (HasCode (..)) where

import Common

class HasCode t where
  data Code t :: Algebra -> *
  probeCode :: SAlgebra a -> Code t a
