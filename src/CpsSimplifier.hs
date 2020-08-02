{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CpsSimplifier (Simplifier, extract) where

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

data TermC t (a :: Algebra) where
  NothingC :: TermC t a

data TermD t a where
  ThunkD :: SAlgebra a -> (Stack t a -> Code t 'Void) -> TermD t ('U a)
  NothingD :: TermD t a

data TermS t a where
  ApplyS :: Data t a -> Stack t b -> TermS t (a ':=> b)
  LetToS :: SSet a -> (Data t a -> Code t 'Void) -> TermS t ('F a)
  NothingS :: TermS t a

c :: Code t a -> Code (Simplifier t) a
c = C NothingC

d :: Data t a -> Data (Simplifier t) a
d = D NothingD

s :: Stack t a -> Stack (Simplifier t) a
s = S NothingS

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a = C (TermC t a) (Code t a)

instance HasData (Simplifier t) where
  data Data (Simplifier t) a = D (TermD t a) (Data t a)

instance HasStack (Simplifier t) where
  data Stack (Simplifier t) a = S (TermS t a) (Stack t a)

instance HasConstants t => HasConstants (Simplifier t) where
  constant = d . constant

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = c . whereIs (abstract . f . d) . extractData

instance HasLabel t => HasLabel (Simplifier t) where
  label (S _ x) f = c $ label x (abstract . f . s)

instance HasTuple t => HasTuple (Simplifier t) where
  pair (D _ x) (D _ y) = d $ pair x y
  unpair (D _ tuple) f = c $ unpair tuple $ \x y -> abstract (f (d x) (d y))

instance (HasLabel t, HasThunk t) => HasThunk (Simplifier t) where
  thunk t f =
    let f' = abstract . f . s
     in D (ThunkD t f') (thunk t f')

  force (D (ThunkD _ f) _) (S _ x) = c $ label x f
  force (D _ x) (S _ k) = c $ force x k

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns (D _ x) (S (LetToS _ f) _) = c $ letBe x f
  returns (D _ x) (S _ k) = c $ returns x k

  letTo t f =
    let f' = abstract . f . d
     in S (LetToS t f') (letTo t f')

instance (HasFn t, HasLet t, HasLabel t) => HasFn (Simplifier t) where
  D _ x <*> S _ k = S (ApplyS x k) (x <*> k)
  lambda (S (ApplyS x t) _) f = c $ label t $ \t' ->
    letBe x $ \x' ->
      abstract (f (d x') (s t'))
  lambda (S _ k) f = c $ lambda k $ \x t -> abstract (f (d x) (s t))

instance HasCall t => HasCall (Simplifier t) where
  call g = d $ call g

abstract :: Code (Simplifier t) a -> Code t a
abstract (C _ code) = code

extractData :: Data (Simplifier t) a -> Data t a
extractData (D _ x) = x
