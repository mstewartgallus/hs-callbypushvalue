{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasThunk (HasThunk (..)) where

import Common
import Global
import HasCode
import HasData
import HasStack

class (HasData t, HasCode t, HasStack t) => HasThunk t where
  thunk :: SAlgebra a -> (Stack t a -> Code t Void) -> Data t (U a)
  force :: Data t (U a) -> Stack t a -> Code t Void

  lambda :: Stack t (a :=> b) -> (Data t a -> Stack t b -> Code t c) -> Code t c

  call :: Global a -> Stack t a -> Code t Void
