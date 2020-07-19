{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CallccSimplifier (Simplifier, simplifyExtract) where

import Callcc
import Common
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasStack
import HasThunk
import HasTuple

simplifyExtract :: Callcc t => Code (Simplifier t) a -> Code t a
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

instance HasStack (Simplifier t) where
  newtype Stack (Simplifier t) a = S (Stack t a)

instance Callcc t => HasConstants (Simplifier t) where
  constant k = D $ constant k
  unit = D unit

instance Callcc t => HasReturn (Simplifier t) where
  returns value = ReturnC $ abstractD value

instance Callcc t => HasLet (Simplifier t) where
  letBe x f = C $ letBe (abstractD x) $ \x' -> abstract (f (D x'))

instance Callcc t => HasLetTo (Simplifier t) where
  letTo (ReturnC x) f = C $ letBe x $ \x' -> abstract (f (D x'))
  letTo x f =
    let
     in C $ letTo (abstract x) $ \x' -> abstract (f (D x'))

  apply (LambdaC _ f) x = C $ letBe (abstractD x) f
  apply f x = C $ apply (abstract f) (abstractD x)

instance Callcc t => HasTuple (Simplifier t)

instance Callcc t => HasThunk (Simplifier t) where
  thunk t f = D $ thunk t $ \x -> abstract (f (S x))
  force x k = C $ force (abstractD x) (abstractS k)

  -- lambda :: Stack t (a :=> b) -> (Data t a -> Stack t b -> Code t c) -> Code t c
  lambda k f = C $ lambda (abstractS k) $ \x t -> abstract (f (D x) (S t))

  call g k = C $ call g (abstractS k)

instance Callcc t => Callcc (Simplifier t) where
  catch t f = C $ catch t $ \x -> abstract (f (S x))
  throw k f = C $ throw (abstractS k) (abstract f)

abstract :: Callcc t => Code (Simplifier t) a -> Code t a
abstract code = case code of
  ReturnC value -> returns value
  C c -> c

abstractD :: Callcc t => Data (Simplifier t) a -> Data t a
abstractD x = case x of
  D d -> d

abstractS :: Callcc t => Stack (Simplifier t) a -> Stack t a
abstractS (S x) = x
