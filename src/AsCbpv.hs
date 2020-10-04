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
import HasTerm
import HasTuple
import NatTrans
import qualified SystemF as F
import Prelude hiding ((<*>))

extract :: Term (AsCbpv t) :~> Code t
extract = NatTrans unC

newtype AsCbpv t = AsCbpv t

instance HasCode t => HasTerm (AsCbpv t) where
  newtype Term (AsCbpv t) a = C {unC :: Code t a}

instance (HasReturn t, HasConstants t) => F.HasConstants (AsCbpv t) where
  constant = C . returns . constant

instance HasCall t => F.HasCall (AsCbpv t) where
  call = C . call

instance (HasLet t, HasTuple t, HasThunk t, HasReturn t) => F.HasTuple (AsCbpv t) where
  pair f g (C x) =
    C $
      letBe (thunk x) $
        returns . pair (thunk . unC . f . C . force) (thunk . unC . g . C . force)
  first = C . from (force . first) . unC
  second = C . from (force . second) . unC

instance (HasLet t, HasThunk t) => F.HasLet (AsCbpv t) where
  whereIs f = C . whereIs (unC . f . C . force) . thunk . unC

instance (HasThunk t, HasFn t) => F.HasFn (AsCbpv t) where
  lambda t f = C $ lambda (SU t) (unC . f . C . force)
  (<*>) (C f) = C . (<*>) f . thunk . unC
