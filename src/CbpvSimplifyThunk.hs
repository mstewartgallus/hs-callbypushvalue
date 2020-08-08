{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyThunk (Simplifier, extract) where

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
  ForceCtx :: HasThunk t => Ctx t (U a) (Code t a)
  IdCtx :: Ctx t a (Data t a)

cin :: Code t a -> Code (Simplifier t) a
cin = C

cout :: Code (Simplifier t) a -> Code t a
cout (C x) = x

din :: Data t a -> Data (Simplifier t) a
din val = D $ \ctx -> case ctx of
  ForceCtx -> force val
  IdCtx -> val

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x IdCtx

instance HasThunk t => HasThunk (Simplifier t) where
  force (D x) = cin $ x $ ForceCtx
  thunk (C x) = D $ \ctx -> case ctx of
    IdCtx -> thunk x
    ForceCtx -> x

instance HasReturn t => HasReturn (Simplifier t) where
  returns = cin . returns . dout
  from f = cin . from (cout . f . din) . cout

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (Code t a)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (forall b. Ctx t a b -> b)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasTuple t => HasTuple (Simplifier t)

instance HasFn t => HasFn (Simplifier t) where
  lambda t f = cin $ lambda t (cout . f . din)
  f <*> x = cin $ (cout f <*> dout x)
