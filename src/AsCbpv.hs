{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import NatTrans
import qualified SystemF as F
import Prelude hiding ((<*>))

extract :: Code (AsCbpv t) :~> Code t
extract = NatTrans unC

newtype AsCbpv t = AsCbpv t deriving (HasCall)

instance HasCode t => HasCode (AsCbpv t) where
  newtype Code (AsCbpv t) a = C {unC :: Code t a}

instance HasData t => HasData (AsCbpv t) where
  newtype Data (AsCbpv t) a = D {unD :: Data t a}

instance (HasReturn t, HasConstants t) => F.HasConstants (AsCbpv t) where
  constant = C . returns . constant

instance HasReturn t => HasReturn (AsCbpv t) where
  returns = C . returns . unD
  from f = C . from (unC . f . D) . unC

instance (HasTuple t, HasThunk t, HasReturn t) => F.HasTuple (AsCbpv t) where
  pair (C x) (C y) = C $ returns (pair (thunk x) (thunk y))
  ofPair f = C . from (ofPair (\x y -> unC $ f (C (force x)) (C (force y)))) . unC

instance (HasLet t, HasThunk t) => F.HasLet (AsCbpv t) where
  whereIs f = C . whereIs (unC . f . C . force) . thunk . unC

instance (HasThunk t, HasFn t) => F.HasFn (AsCbpv t) where
  lambda t f = C $ lambda (SU t) (unC . f . C . force)
  (<*>) (C f) = C . (<*>) f . thunk . unC
