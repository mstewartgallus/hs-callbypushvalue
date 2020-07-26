{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifier (Simplifier, extract) where

import Cbpv
import Common
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple

extract :: Data (Simplifier t) a -> Data t a
extract = abstractD

data Simplifier t

data TermC t a where
  LambdaC :: SSet a -> (Data t a -> Code t b) -> TermC t (a ':=> b)
  ForceC :: Data t ('U a) -> TermC t a
  ReturnC :: Data t a -> TermC t ('F a)
  NothingC :: TermC t a

data TermD t a where
  ThunkD :: Code t a -> TermD t ('U a)
  NothingD :: TermD t a

c = C NothingC

d = D NothingD

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a = C (TermC t a) (Code t a)

instance HasData (Simplifier t) where
  data Data (Simplifier t) a = D (TermD t a) (Data t a)

instance Cbpv t => HasConstants (Simplifier t) where
  constant k = d $ constant k

instance HasCall t => HasCall (Simplifier t) where
  call g = c $ call g

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns (D _ value) = C (ReturnC value) $ returns value
  letTo (C (ReturnC x) _) f = c $ letBe x $ \x' -> abstract (f (d x'))
  letTo (C _ x) f = c $ letTo x $ \x' -> abstract (f (d x'))

instance HasLet t => HasLet (Simplifier t) where
  letBe (D _ x) f = c $ letBe x $ \x' -> abstract (f (d x'))

instance HasTuple t => HasTuple (Simplifier t) where
  pair (D _ x) (D _ y) = d $ pair x y
  unpair (D _ tuple) f = c $ unpair tuple $ \x y -> abstract (f (d x) (d y))

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' x = abstract (f (d x))
     in C (LambdaC t f') $ lambda t f'

  apply (C (LambdaC _ f) _) (D _ x) = c $ letBe x f
  apply (C _ f) (D _ x) = c $ apply f x

instance HasThunk t => HasThunk (Simplifier t) where
  force (D (ThunkD code) _) = c code
  force (D _ th) = C (ForceC th) (force th)

  thunk (C (ForceC x) _) = d x
  thunk (C _ code) = D (ThunkD code) (thunk code)

abstract :: Code (Simplifier t) a -> Code t a
abstract (C _ code) = code

abstractD :: Data (Simplifier t) a -> Data t a
abstractD (D _ x) = x
