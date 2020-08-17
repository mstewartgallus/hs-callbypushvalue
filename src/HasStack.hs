{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasStack (HasStack (..)) where

import Common

class HasStack t where
  data Stack t :: Algebra -> *
  probeStack :: SAlgebra a -> Stack t a
