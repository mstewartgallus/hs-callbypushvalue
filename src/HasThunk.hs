{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module HasThunk (HasThunk (..)) where

import Common
import HasCode
import HasData

class (HasCode t, HasData t) => HasThunk t where
  thunk :: Code t a -> Data t ('U a)
  force :: Data t ('U a) -> Code t a
