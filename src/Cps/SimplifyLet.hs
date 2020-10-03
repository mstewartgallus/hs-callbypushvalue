{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cps.SimplifyLet (Simplifier, extract) where

import Common
import Cps
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTerminal
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Data (Simplifier t) :~> Data t
extract = NatTrans dout

data Simplifier t

data TermS t a where
  LetToS :: SSet a -> (Data t a -> Code t Void) -> TermS t (F a)
  NothingS :: TermS t a

cin :: Code t a -> Code (Simplifier t) a
cin = C

cout :: Code (Simplifier t) a -> Code t a
cout (C x) = x

din :: Data t a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x

kin :: Stack t a -> Stack (Simplifier t) a
kin = S NothingS

sout :: Stack (Simplifier t) a -> Stack t a
sout (S _ x) = x

instance HasCode t => HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (Code t a)
  probeCode t = C (probeCode t)

instance HasData t => HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)
  probeData t = D (probeData t)

instance HasStack t => HasStack (Simplifier t) where
  data Stack (Simplifier t) a = S (TermS t a) (Stack t a)
  probeStack t = S NothingS (probeStack t)

instance HasConstants t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasTerminal t => HasTerminal (Simplifier t) where
  terminal = din terminal

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasLabel t => HasLabel (Simplifier t) where
  whereLabel f = cin . whereLabel (cout . f . kin) . sout

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = din . pair (dout . f . din) (dout . g . din) . dout
  first = din . first . dout
  second = din . second . dout

instance HasThunk t => HasThunk (Simplifier t) where
  thunk t f = din $ thunk t (cout . f . kin)
  force x k = cin $ force (dout x) (sout k)

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns x (S (LetToS _ f) _) = cin $ letBe (dout x) f
  returns x k = cin $ returns (dout x) (sout k)

  letTo t f =
    let f' = cout . f . din
     in S (LetToS t f') (letTo t f')

instance HasFn t => HasFn (Simplifier t) where
  x <*> k = kin (dout x <*> sout k)
  lambda k f = cin $ lambda (sout k) $ \x t -> cout (f (din x) (kin t))

instance HasCall t => HasCall (Simplifier t) where
  call = din . call
