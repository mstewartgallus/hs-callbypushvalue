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
  returns value = C (ReturnC $ abstractD value) $ returns $ abstractD value
  letTo (C (ReturnC x) _) f = c $ letBe x $ \x' -> abstract (f (d x'))
  letTo x f = c $ letTo (abstract x) $ \x' -> abstract (f (d x'))

instance HasLet t => HasLet (Simplifier t) where
  letBe x f = c $ letBe (abstractD x) $ \x' -> abstract (f (d x'))

instance HasTuple t => HasTuple (Simplifier t) where
  pair x y = d $ pair (abstractD x) (abstractD y)
  unpair tuple f = c $ unpair (abstractD tuple) $ \x y -> abstract (f (d x) (d y))

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f = C (LambdaC t $ \x -> abstract (f (d x))) $ lambda t $ \x -> abstract (f (d x))

  apply (C (LambdaC _ f) _) x = c $ letBe (abstractD x) f
  apply f x = c $ apply (abstract f) (abstractD x)

instance HasThunk t => HasThunk (Simplifier t) where
  force (D (ThunkD code) _) = c code
  force th = C (ForceC (abstractD th)) (force (abstractD th))

  thunk (C (ForceC x) _) = d x
  thunk code = D (ThunkD (abstract code)) $ thunk $ abstract code

abstract :: Code (Simplifier t) a -> Code t a
abstract (C _ code) = code

abstractD :: Data (Simplifier t) a -> Data t a
abstractD (D _ x) = x
