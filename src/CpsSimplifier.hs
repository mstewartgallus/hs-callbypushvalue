{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CpsSimplifier (Simplifier, simplifyExtract) where

import Common
import Cps
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetLabel
import HasReturn
import HasStack
import HasThunk
import HasTuple

simplifyExtract :: Cps t => Data (Simplifier t) a -> Data t a
simplifyExtract term = abstractD term

data Simplifier t

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a where
    C :: Code t a -> Code (Simplifier t) a

instance HasData (Simplifier t) where
  data Data (Simplifier t) a where
    ThunkD :: SAlgebra a -> (Stack t a -> Code t Void) -> Data (Simplifier t) (U a)
    D :: Data t a -> Data (Simplifier t) a

instance HasStack (Simplifier t) where
  data Stack (Simplifier t) a where
    LetToS :: SSet a -> (Data t a -> Code t Void) -> Stack (Simplifier t) (F a)
    S :: Stack t a -> Stack (Simplifier t) a

instance Cps t => HasConstants (Simplifier t) where
  constant k = D $ constant k
  unit = D unit

instance Cps t => HasLet (Simplifier t) where
  letBe x f = C $ letBe (abstractD x) $ \x' -> abstract (f (D x'))

instance Cps t => HasLetLabel (Simplifier t) where
  letLabel x f = C $ letLabel (abstractS x) $ \x' -> abstract (f (S x'))

instance Cps t => HasTuple (Simplifier t)

instance Cps t => HasThunk (Simplifier t) where
  thunk t f = ThunkD t $ \x -> abstract (f (S x))
  force (ThunkD _ f) x = C $ letLabel (abstractS x) f
  force x k = C $ force (abstractD x) (abstractS k)

  lambda k f = C $ lambda (abstractS k) $ \x t -> abstract (f (D x) (S t))

  call g k = C $ call g (abstractS k)

instance Cps t => Cps (Simplifier t) where
  throw (LetToS _ f) x = C $ letBe (abstractD x) f
  throw k x = C $ throw (abstractS k) (abstractD x)

  letTo t f = LetToS t $ \x -> abstract (f (D x))

  apply x f = S $ apply (abstractD x) (abstractS f)

-- nil :: Stack t Void
-- ThrowC (ToS binder body) value -> simpC (LetBeC value binder body)
-- ForceC (ThunkD label body) k -> simpC (LetLabelC k label body)

abstract :: Cps t => Code (Simplifier t) a -> Code t a
abstract code = case code of
  C c -> c

abstractD :: Cps t => Data (Simplifier t) a -> Data t a
abstractD x = case x of
  ThunkD t f -> thunk t f
  D d -> d

abstractS :: Cps t => Stack (Simplifier t) a -> Stack t a
abstractS x = case x of
  LetToS t f -> letTo t f
  S s -> s
