{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyReturn (Simplifier, extract) where

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

data Ctx t (a :: Algebra) (b :: Algebra) where
  LetToCtx :: HasReturn t => (Data t a -> Code t b) -> Ctx t (F a) b
  IdCtx :: Ctx t a a

cin :: Code t a -> Code (Simplifier t) a
cin code = C $ \ctx -> case ctx of
  LetToCtx f -> from f code
  IdCtx -> code

cout :: Code (Simplifier t) a -> Code t a
cout (C f) = f IdCtx

din :: Data t a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns x =
    let x' = dout x
     in C $ \ctx -> case ctx of
          IdCtx -> returns x'
          LetToCtx f -> whereIs f x'

  from f (C x) = C $ \ctx -> x $ LetToCtx $ \x' -> case f (din x') of
    C y -> y ctx

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (forall b. Ctx t a b -> Code t b)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f x = C $ \ctx -> letBe (dout x) $ \x' -> case f (din x') of
    C y -> y ctx

instance HasTuple t => HasTuple (Simplifier t)

instance HasFn t => HasFn (Simplifier t) where
  lambda t f = cin $ lambda t (cout . f . din)
  f <*> x = cin $ (cout f <*> dout x)

instance HasThunk t => HasThunk (Simplifier t) where
  force = cin . force . dout
  thunk = din . thunk . cout
