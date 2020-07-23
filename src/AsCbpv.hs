{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCbpv (extract, AsCbpv) where

import Cbpv
import Common
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasTuple
import qualified SystemF as F

extract :: Code (AsCbpv t) a -> Code t a
extract (C x) = x

data AsCbpv t

instance HasCode t => HasCode (AsCbpv t) where
  newtype Code (AsCbpv t) a = C (Code t a)

instance HasData t => HasData (AsCbpv t) where
  newtype Data (AsCbpv t) a = D (Data t a)

instance HasGlobals t => HasGlobals (AsCbpv t) where
  global g = C (global g)

instance HasConstants t => HasConstants (AsCbpv t) where
  unit = D unit
  constant k = D (constant k)

instance HasReturn t => HasReturn (AsCbpv t) where
  returns (D k) = C (returns k)

instance Cbpv t => F.SystemF (AsCbpv t) where
  pair (C x) (C y) = C $ returns (pair (thunk x) (thunk y))
  unpair (C tuple) f = C $ letTo tuple $ \tuple' ->
    unpair tuple' $ \x y -> case f (C (Cbpv.force x)) (C (Cbpv.force y)) of
      C r -> r

  letBe (C x) f = C $ letBe (Cbpv.thunk x) $ \x' ->
    let C body = f (C (Cbpv.force x'))
     in body
  lambda t f = C $ lambda (SU t) $ \x ->
    let C body = f (C (force x))
     in body
  C f <*> C x = C $ apply f (thunk x)
