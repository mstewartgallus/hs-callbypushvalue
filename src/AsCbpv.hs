{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCbpv (extract, AsCbpv) where

import Cbpv
import Common
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple
import qualified SystemF as F

extract :: Code (AsCbpv t) a -> Code t a
extract (C x) = x

data AsCbpv t

instance HasCode t => HasCode (AsCbpv t) where
  newtype Code (AsCbpv t) a = C (Code t a)

instance HasData t => HasData (AsCbpv t) where
  newtype Data (AsCbpv t) a = D (Data t a)

instance HasCall t => HasCall (AsCbpv t) where
  call g = C (call g)

instance HasConstants t => HasConstants (AsCbpv t) where
  unit = D unit
  constant k = D (constant k)

instance HasReturn t => HasReturn (AsCbpv t) where
  returns (D k) = C (returns k)

instance (HasTuple t, HasThunk t, HasReturn t) => F.HasTuple (AsCbpv t) where
  pair (C x) (C y) = C $ returns (pair (thunk x) (thunk y))
  unpair (C tuple) f = C $ letTo tuple $ \tuple' ->
    unpair tuple' $ \x y -> case f (C (force x)) (C (force y)) of
      C r -> r

instance Cbpv t => F.SystemF (AsCbpv t) where
  letBe (C x) f = C $ letBe (thunk x) $ \x' ->
    let C body = f (C (force x'))
     in body

instance (HasThunk t, HasFn t) => F.HasFn (AsCbpv t) where
  lambda t f = C $ lambda (SU t) $ \x ->
    let C body = f (C (force x))
     in body
  C f <*> C x = C $ apply f (thunk x)
