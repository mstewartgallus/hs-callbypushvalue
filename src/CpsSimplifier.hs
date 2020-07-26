{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CpsSimplifier (Simplifier, simplifyExtract) where

import Common
import Cps
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple

simplifyExtract :: Cps t => Data (Simplifier t) a -> Data t a
simplifyExtract = abstractD

data Simplifier t

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a where
    C :: Code t a -> Code (Simplifier t) a

instance HasData (Simplifier t) where
  data Data (Simplifier t) a where
    ThunkD :: SAlgebra a -> (Stack t a -> Code t 'Void) -> Data (Simplifier t) ('U a)
    D :: Data t a -> Data (Simplifier t) a

instance HasStack (Simplifier t) where
  data Stack (Simplifier t) a where
    ApplyS :: Data t a -> Stack t b -> Stack (Simplifier t) (a ':=> b)
    LetToS :: SSet a -> (Data t a -> Code t 'Void) -> Stack (Simplifier t) ('F a)
    S :: Stack t a -> Stack (Simplifier t) a

instance Cps t => HasConstants (Simplifier t) where
  constant k = D $ constant k

instance Cps t => HasLet (Simplifier t) where
  letBe x f = C $ letBe (abstractD x) $ \x' -> abstract (f (D x'))

instance Cps t => HasLabel (Simplifier t) where
  label x f = C $ label (abstractS x) $ \x' -> abstract (f (S x'))

instance Cps t => HasTuple (Simplifier t) where
  pair x y = D $ pair (abstractD x) (abstractD y)
  unpair tuple f = C $ unpair (abstractD tuple) $ \x y -> abstract (f (D x) (D y))

instance Cps t => HasThunk (Simplifier t) where
  thunk t f = ThunkD t $ \x -> abstract (f (S x))

  force (ThunkD _ f) x = C $ label (abstractS x) f
  force x k = C $ force (abstractD x) (abstractS k)

instance Cps t => HasReturn (Simplifier t) where
  returns (LetToS _ f) x = C $ letBe (abstractD x) f
  returns k x = C $ returns (abstractS k) (abstractD x)

  letTo t f = LetToS t $ \x -> abstract (f (D x))

instance Cps t => HasFn (Simplifier t) where
  apply x f = ApplyS (abstractD x) (abstractS f)
  lambda (ApplyS x t) f = C $ label t $ \t' ->
    letBe x $ \x' ->
      abstract (f (D x') (S t'))
  lambda k f = C $ lambda (abstractS k) $ \x t -> abstract (f (D x) (S t))

instance Cps t => HasCall (Simplifier t) where
  call g k = C $ call g (abstractS k)

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
  ApplyS h t -> apply h t
  S s -> s
