{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CpsSimplifyForce (Simplifier, extract) where

import Common
import Cps
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Data (Simplifier t) :~> Data t
extract = NatTrans $ \(D _ x) -> x

data Simplifier t

data TermD t a where
  ThunkD :: SAlgebra a -> (Stack t a -> Code t 'Void) -> TermD t ('U a)
  NothingD :: TermD t a

cin :: Code t a -> Code (Simplifier t) a
cin = C

cout :: Code (Simplifier t) a -> Code t a
cout (C x) = x

din :: Data t a -> Data (Simplifier t) a
din = D NothingD

dout :: Data (Simplifier t) a -> Data t a
dout (D _ x) = x

kin :: Stack t a -> Stack (Simplifier t) a
kin = S

sout :: Stack (Simplifier t) a -> Stack t a
sout (S x) = x

instance (HasLabel t, HasThunk t) => HasThunk (Simplifier t) where
  thunk t f =
    let f' = cout . f . kin
     in D (ThunkD t f') (thunk t f')

  force (D (ThunkD _ f) _) x = cin $ label (sout x) f
  force x k = cin $ force (dout x) (sout k)

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (Code t a)

instance HasData (Simplifier t) where
  data Data (Simplifier t) a = D (TermD t a) (Data t a)

instance HasStack (Simplifier t) where
  newtype Stack (Simplifier t) a = S (Stack t a)

instance HasConstants t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasLabel t => HasLabel (Simplifier t) where
  label x f = cin $ label (sout x) (cout . f . kin)

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = din . pair (dout . f . din) (dout . g . din) . dout
  first = din . first . dout
  second = din . second . dout

instance HasReturn t => HasReturn (Simplifier t) where
  returns x k = cin $ returns (dout x) (sout k)
  letTo t f = kin $ letTo t (cout . f . din)

instance HasFn t => HasFn (Simplifier t) where
  x <*> k = kin (dout x <*> sout k)
  lambda k f = cin $ lambda (sout k) $ \x t -> cout (f (din x) (kin t))

instance HasCall t => HasCall (Simplifier t) where
  call = din . call
