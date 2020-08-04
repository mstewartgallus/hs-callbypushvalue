{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCbpv (Code, Data, extract) where

import Cbpv
import Common
import HasCall
import HasConstants
import HasLet
import HasTuple
import NatTrans
import qualified Path
import qualified SystemF as F
import Prelude hiding ((<*>))

extract :: Code cd dta :~> cd
extract = NatTrans unC

newtype Code cd (dta :: Set -> *) (a :: Algebra) = C {unC :: cd a}

newtype Data (cd :: Algebra -> *) dta (a :: Set) = D {unD :: dta a}

instance HasCall cd => HasCall (Code cd dta) where
  call = C . call

instance (HasReturn cd dta, HasConstants dta) => F.HasConstants (Code cd dta) where
  constant = C . returns . constant

instance HasReturn cd dta => HasReturn (Code cd dta) (Data cd dta) where
  returns = C . returns . unD
  from f = C . from (unC . f . D) . unC

instance (HasTuple cd dta, HasThunk cd dta, HasReturn cd dta) => F.HasTuple (Code cd dta) where
  pair (C x) (C y) = C $ returns (pair (thunk x) (thunk y))
  unpair (C tuple) f = C $ letTo tuple $ \tuple' ->
    unpair tuple' $ \x y -> unC $ f (C (force x)) (C (force y))

instance (HasLet cd dta, HasThunk cd dta) => F.HasLet (Code cd dta) where
  whereIs f = C . whereIs (unC . f . C . force) . thunk . unC

instance (HasThunk cd dta, HasFn cd dta) => F.HasFn (Code cd dta) where
  lambda t f = C $ lambda (SU t) (unC . Path.flatten f . C . force)
  (<*>) (C f) = C . (<*>) f . thunk . unC
