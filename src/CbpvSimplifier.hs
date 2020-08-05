{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
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
extract = NatTrans abstract

data Simplifier t

data family TermC t (a :: Algebra)

data family TermD t (a :: Set)

c :: Code t a -> Code (Simplifier t) a
c = C Nothing

d :: Data t a -> Data (Simplifier t) a
d = D Nothing

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a = C (Maybe (TermC t a)) (Code t a)

instance HasData (Simplifier t) where
  data Data (Simplifier t) a = D (Maybe (TermD t a)) (Data t a)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = d . constant

instance HasCall t => HasCall (Simplifier t) where
  call = c . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f (D _ x) = c $ whereIs (abstract . f . d) x

instance HasTuple t => HasTuple (Simplifier t) where
  pair (D _ x) (D _ y) = d $ pair x y
  ofPair f (D _ tuple) = c $ unpair tuple (\x y -> abstract (f (d x) (d y)))

newtype instance TermC t ('F a) = ReturnC (Data t a)

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns (D _ value) = C (Just (ReturnC value)) $ returns value
  from f (C (Just (ReturnC x)) _) = c $ whereIs (abstract . f . d) x
  from f (C _ x) = c $ from (abstract . f . d) x

data instance TermC t (a ':=> b) = LambdaC (SSet a) (Data t a -> Code t b)

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' = abstract . f . d
     in C (Just (LambdaC t f')) $ lambda t f'

  C (Just (LambdaC _ f)) _ <*> D _ x = c $ letBe x f
  C _ f <*> D _ x = c $ f <*> x

newtype instance TermD t ('U a) = ThunkD (Code t a)

instance HasThunk t => HasThunk (Simplifier t) where
  force (D (Just (ThunkD code)) _) = c code
  force (D _ th) = c (force th)

  -- fixme .. pass in thunk info somehow?
  thunk (C _ code) = D (Just (ThunkD code)) (thunk code)

abstract :: Code (Simplifier t) a -> Code t a
abstract (C _ code) = code
