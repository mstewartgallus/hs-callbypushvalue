{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifier (Simplifier, simplifyExtract) where

import Cbpv
import Common
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasTuple

simplifyExtract :: Cbpv t => Code (Simplifier t) a -> Code t a
simplifyExtract term = abstract term

data Simplifier t

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a where
    LambdaC :: SSet a -> (Data t a -> Code t b) -> Code (Simplifier t) (a :=> b)
    ForceC :: Data t (U a) -> Code (Simplifier t) a
    ReturnC :: Data t a -> Code (Simplifier t) (F a)
    C :: Code t a -> Code (Simplifier t) a

instance HasData (Simplifier t) where
  data Data (Simplifier t) a where
    ThunkD :: Code t a -> Data (Simplifier t) (U a)
    D :: Data t a -> Data (Simplifier t) a

instance Cbpv t => HasGlobals (Simplifier t) where
  global g = C $ global g

instance Cbpv t => HasConstants (Simplifier t) where
  constant k = D $ constant k
  unit = D $ unit

instance Cbpv t => HasReturn (Simplifier t) where
  returns value = ReturnC $ abstractD value

instance Cbpv t => HasLet (Simplifier t) where
  letBe x f = C $ letBe (abstractD x) $ \x' -> abstract (f (D x'))

instance Cbpv t => HasLetTo (Simplifier t) where
  letTo (ReturnC x) f = C $ letBe x $ \x' -> abstract (f (D x'))
  letTo x f =
    let
     in C $ letTo (abstract x) $ \x' -> abstract (f (D x'))

  apply (LambdaC _ f) x = C $ letBe (abstractD x) f
  apply f x = C $ apply (abstract f) (abstractD x)

instance Cbpv t => HasTuple (Simplifier t)

instance Cbpv t => Cbpv (Simplifier t) where
  lambda t f = LambdaC t $ \x -> abstract (f (D x))

  force (ThunkD code) = C code
  force thunk = ForceC (abstractD thunk)

  thunk (ForceC x) = D x
  thunk code = ThunkD (abstract code)

abstract :: Cbpv t => Code (Simplifier t) a -> Code t a
abstract code = case code of
  ForceC x -> force x
  LambdaC t f -> lambda t f
  ReturnC value -> returns value
  C c -> c

abstractD :: Cbpv t => Data (Simplifier t) a -> Data t a
abstractD x = case x of
  ThunkD x -> thunk x
  D d -> d
