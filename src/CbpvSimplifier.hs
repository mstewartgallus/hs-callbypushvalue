{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifier (Code, Data, extract) where

import Cbpv
import Common
import HasCall
import HasConstants
import HasLet
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Code cd dta :~> cd
extract = NatTrans $ \(C _ code) -> code

data family TermC (cd :: Algebra -> *) (dta :: Set -> *) (a :: Algebra)

data family TermD (cd :: Algebra -> *) (dta :: Set -> *) (a :: Set)

data Code cd dta a = C (Maybe (TermC cd dta a)) (cd a)

data Data cd dta a = D (Maybe (TermD cd dta a)) (dta a)

newtype instance TermC cd dta ('F a) = ReturnC (dta a)

data instance TermC cd dta (a ':=> b) = LambdaC (SSet a) (dta a -> cd b)

newtype instance TermD cd dta ('U a) = ThunkD (cd a)

c :: cd a -> Code cd dta a
c = C Nothing

d :: dta a -> Data cd dta a
d = D Nothing

instance HasConstants dta => HasConstants (Data cd dta) where
  constant = d . constant

instance HasCall cd => HasCall (Code cd dta) where
  call = c . call

instance HasLet cd dta => HasLet (Code cd dta) (Data cd dta) where
  whereIs f (D _ x) = c $ whereIs (abstract . f . d) x

instance HasTuple cd dta => HasTuple (Code cd dta) (Data cd dta) where
  pair (D _ x) (D _ y) = d $ pair x y
  ofPair f (D _ tuple) = c $ unpair tuple (\x y -> abstract (f (d x) (d y)))

instance (HasLet cd dta, HasReturn cd dta) => HasReturn (Code cd dta) (Data cd dta) where
  returns (D _ value) = C (Just (ReturnC value)) $ returns value
  from f (C (Just (ReturnC x)) _) = c $ whereIs (abstract . f . d) x
  from f (C _ x) = c $ from (abstract . f . d) x

instance (HasLet cd dta, HasFn cd dta) => HasFn (Code cd dta) (Data cd dta) where
  lambda t f =
    let f' = abstract . f . d
     in C (Just (LambdaC t f')) $ lambda t f'

  C (Just (LambdaC _ f)) _ <*> D _ x = c $ letBe x f
  C _ f <*> D _ x = c $ f <*> x

instance HasThunk cd dta => HasThunk (Code cd dta) (Data cd dta) where
  force (D (Just (ThunkD code)) _) = c code
  force (D _ th) = c (force th)

  -- fixme .. pass in thunk info somehow?
  thunk (C _ code) = D (Just (ThunkD code)) (thunk code)

abstract :: Code cd dta a -> cd a
abstract (C _ code) = code

abstractD :: Data cd dta a -> dta a
abstractD (D _ x) = x
