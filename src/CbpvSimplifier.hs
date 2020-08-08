{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifier (Simplifier, extract) where

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

data CtxC t (a :: Algebra) (b :: Algebra) where
  ApplyCtxC :: HasFn t => Data t a -> CtxC t (a :=> b) b
  LetToCtxC :: HasReturn t => (Data t a -> Code t b) -> CtxC t (F a) b
  IdCtxC :: CtxC t a a

data CtxD t (a :: Set) (b :: Set) where
  IdCtxD :: CtxD t a a

cin :: Code t a -> Code (Simplifier t) a
cin code = C $ \ctx -> case ctx of
  LetToCtxC f -> from f code
  ApplyCtxC x -> code <*> x
  IdCtxC -> code

cout :: Code (Simplifier t) a -> Code t a
cout (C f) = f IdCtxC

din :: Data t a -> Data (Simplifier t) a
din val = D $ \ctx -> case ctx of
  IdCtxD -> val

dout :: Data (Simplifier t) a -> Data t a
dout (D f) = f IdCtxD

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (forall b. CtxC t a b -> Code t b)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (forall b. CtxD t a b -> Data t b)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasTuple t => HasTuple (Simplifier t)

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns x =
    let x' = dout x
     in C $ \ctx -> case ctx of
          IdCtxC -> returns x'
          LetToCtxC f -> whereIs f x'

  from f (C x) = cin $ x $ LetToCtxC (cout . f . din)

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' = cout . f . din
     in C $ \ctx -> case ctx of
          IdCtxC -> lambda t f'
          ApplyCtxC x -> whereIs f' x

  C f <*> x = cin $ f $ ApplyCtxC $ dout x

instance HasThunk t => HasThunk (Simplifier t) where
  force = cin . force . dout
  thunk = din . thunk . cout
