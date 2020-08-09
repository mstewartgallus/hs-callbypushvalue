{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyApply (Simplifier, extract) where

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
  ApplyCtx :: HasFn t => Data t a -> Ctx t (a :=> b) b
  IdCtx :: Ctx t a a

cin :: Code t a -> Code (Simplifier t) a
cin code = C $ \ctx -> case ctx of
  ApplyCtx x -> code <*> x
  IdCtx -> code

cout :: Code (Simplifier t) a -> Code t a
cout (C f) = f IdCtx

din :: Data t a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' = cout . f . din
     in C $ \ctx -> case ctx of
          IdCtx -> lambda t f'
          ApplyCtx x -> whereIs f' x
  (<*>) (C f) = cin . f . ApplyCtx . dout

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (forall b. Ctx t a b -> Code t b)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f (D x) = C $ \ctx -> letBe x $ \x' ->
    case f (din x') of
      C y -> y ctx

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = din . pair (dout . f . din) (dout . g . din) . dout
  first = din . first . dout
  second = din . second . dout

instance HasReturn t => HasReturn (Simplifier t) where
  returns = cin . returns . dout
  from f x = C $ \ctx -> letTo (cout x) $ \x' ->
    case f (din x') of
      C y -> y ctx

instance HasThunk t => HasThunk (Simplifier t) where
  force = cin . force . dout
  thunk = din . thunk . cout
