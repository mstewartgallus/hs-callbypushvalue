{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasCpsThunk (HasCpsThunk (..)) where

import Common
import HasCode
import HasData
import HasStack

-- | Decomposition of thunks into cps style
class (HasData t, HasCode t, HasStack t) => HasCpsThunk t where
  thunk :: SAlgebra a -> (Stack t a -> Code t 'Void) -> Data t ('U a)
  force :: Data t ('U a) -> Stack t a -> Code t 'Void
