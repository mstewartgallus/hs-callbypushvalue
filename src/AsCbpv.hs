{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCbpv (extract, AsCbpv) where

import Cbpv
import Common
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple
import qualified SystemF as F
import Prelude hiding ((<*>))

extract :: Code (AsCbpv t) a -> Code t a
extract (C x) = x

data AsCbpv t

instance HasCode t => HasCode (AsCbpv t) where
  newtype Code (AsCbpv t) a = C (Code t a)

instance HasData t => HasData (AsCbpv t) where
  newtype Data (AsCbpv t) a = D (Data t a)

instance HasCall t => HasCall (AsCbpv t) where
  call g = C (call g)

instance (HasReturn t, HasConstants t) => F.HasConstants (AsCbpv t) where
  constant k = C (returns (constant k))

instance HasReturn t => HasReturn (AsCbpv t) where
  returns (D k) = C (returns k)
  letTo (C x) f = C $ letTo x $ \x' -> case f (D x') of
    C y -> y

instance (HasTuple t, HasThunk t, HasReturn t) => F.HasTuple (AsCbpv t) where
  pair (C x) (C y) = C $ returns (pair (thunk x) (thunk y))
  unpair (C tuple) f = C $ letTo tuple $ \tuple' ->
    unpair tuple' $ \x y -> case f (C (force x)) (C (force y)) of
      C r -> r

instance (HasLet t, HasThunk t) => F.HasLet (AsCbpv t) where
  letBe (C x) f = C $ letBe (thunk x) $ \x' ->
    let C body = f (C (force x'))
     in body

instance (HasThunk t, HasFn t) => F.HasFn (AsCbpv t) where
  lambda t f = C $ lambda (SU t) $ \x ->
    let C body = f (C (force x))
     in body
  C f <*> C x = C (f <*> thunk x)
