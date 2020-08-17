{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasStack (HasStack (..)) where

import Common
import Data.Kind

class HasStack t where
  data Stack t :: Algebra -> Type
  probeStack :: SAlgebra a -> Stack t a
