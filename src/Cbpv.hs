{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cbpv (Cbpv, HasReturn (..), HasFn (..), HasThunk (..)) where

import Common
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple

class (HasCall t, HasConstants t, HasLet t, HasReturn t, HasThunk t, HasFn t, HasTuple t) => Cbpv t

instance (HasCall t, HasConstants t, HasLet t, HasReturn t, HasThunk t, HasFn t, HasTuple t) => Cbpv t

class (HasData t, HasCode t) => HasReturn t where
  letTo :: Code t ('F a) -> (Data t a -> Code t b) -> Code t b
  returns :: Data t a -> Code t ('F a)

class (HasData t, HasCode t) => HasFn t where
  lambda :: SSet a -> (Data t a -> Code t b) -> Code t (a ':=> b)
  (<*>) :: Code t (a ':=> b) -> Data t a -> Code t b

infixl 4 <*>

class (HasCode t, HasData t) => HasThunk t where
  thunk :: Code t a -> Data t ('U a)
  force :: Data t ('U a) -> Code t a
