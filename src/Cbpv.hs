{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (Cbpv, HasReturn (..), HasFn (..), HasThunk (..)) where

import Common
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple

type Cbpv t = (HasCall t, HasConstants t, HasLet t, HasReturn t, HasThunk t, HasFn t, HasTuple t)

class (HasData t, HasCode t) => HasReturn t where
  letTo :: Code t ('F a) -> (Data t a -> Code t b) -> Code t b
  letTo = flip from
  from :: (Data t a -> Code t b) -> Code t ('F a) -> Code t b
  from = flip letTo

  returns :: Data t a -> Code t ('F a)

class (HasData t, HasCode t) => HasFn t where
  lambda :: SSet a -> (Data t a -> Code t b) -> Code t (a ':=> b)
  (<*>) :: Code t (a ':=> b) -> Data t a -> Code t b

infixl 4 <*>

class (HasCode t, HasData t) => HasThunk t where
  thunk :: Code t a -> Data t ('U a)
  force :: Data t ('U a) -> Code t a
