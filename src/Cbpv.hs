{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (Cbpv (..)) where

import Common
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasTuple

class (HasGlobals t, HasConstants t, HasLet t, HasLetTo t, HasTuple t, HasReturn t) => Cbpv t where
  lambda :: SSet a -> (Data t a -> Code t b) -> Code t (a ':=> b)
  thunk :: Code t a -> Data t ('U a)
  force :: Data t ('U a) -> Code t a
