{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyForce (Simplifier, extract) where

import Cbpv
import Common
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Code (Simplifier t) :~> Code t
extract = NatTrans cout

data Simplifier t

data Ctx t a b where
  ThunkCtx :: HasThunk t => Ctx t a (Data t (U a))
  IdCtx :: Ctx t a (Code t a)

cin :: Code t a -> Code (Simplifier t) a
cin code = C $ \ctx -> case ctx of
  ThunkCtx -> thunk code
  IdCtx -> code

cout :: Code (Simplifier t) a -> Code t a
cout (C f) = f IdCtx

din :: Data t a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x

instance HasThunk t => HasThunk (Simplifier t) where
  thunk (C x) = din $ x $ ThunkCtx
  force (D x) = C $ \ctx -> case ctx of
    IdCtx -> force x
    ThunkCtx -> x

instance HasFn t => HasFn (Simplifier t) where
  lambda t f = cin $ lambda t (cout . f . din)
  f <*> x = cin $ (cout f <*> dout x)

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (forall b. Ctx t a b -> b)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasTuple t => HasTuple (Simplifier t)

instance HasReturn t => HasReturn (Simplifier t) where
  returns = cin . returns . dout
  from f = cin . from (cout . f . din) . cout
