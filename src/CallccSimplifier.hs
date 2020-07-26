{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CallccSimplifier (Simplifier, extract) where

import Callcc
import Common
import Cps (HasThunk (..))
import HasCode
import HasConstants
import HasData
import HasFn
import HasGlobals
import HasLet
import HasReturn
import HasStack
import HasTuple

extract :: Callcc t => Data (Simplifier t) a -> Data t a
extract = abstractD

data Simplifier t

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a where
    ReturnC :: Data t a -> Code (Simplifier t) ('F a)
    C :: Code t a -> Code (Simplifier t) a

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)

instance HasStack (Simplifier t) where
  newtype Stack (Simplifier t) a = S (Stack t a)

instance Callcc t => HasConstants (Simplifier t) where
  constant k = D $ constant k
  unit = D unit

instance Callcc t => HasLet (Simplifier t) where
  letBe x f = C $ letBe (abstractD x) $ \x' -> abstract (f (D x'))

instance Callcc t => HasReturn (Simplifier t) where
  returns value = ReturnC $ abstractD value
  letTo (ReturnC x) f = C $ letBe x $ \x' -> abstract (f (D x'))
  letTo x f = C $ letTo (abstract x) $ \x' -> abstract (f (D x'))

instance Callcc t => HasFn (Simplifier t) where
  apply f x = C $ apply (abstract f) (abstractD x)
  lambda t f = C $ lambda t $ \x -> abstract (f (D x))

instance HasGlobals t => HasGlobals (Simplifier t) where
  global g = C $ global g

instance Callcc t => HasTuple (Simplifier t) where
  pair x y = D $ pair (abstractD x) (abstractD y)
  unpair tuple f = C $ unpair (abstractD tuple) $ \x y -> abstract (f (D x) (D y))

instance Callcc t => HasThunk (Simplifier t) where
  thunk t f = D $ thunk t $ \x -> abstract (f (S x))
  force x k = C $ force (abstractD x) (abstractS k)

instance Callcc t => Callcc (Simplifier t) where
  catch t f = C $ catch t $ \x -> abstract (f (S x))
  throw k f = C $ throw (abstractS k) (abstract f)

abstract :: Callcc t => Code (Simplifier t) a -> Code t a
abstract code = case code of
  ReturnC value -> returns value
  C c -> c

abstractD :: Callcc t => Data (Simplifier t) a -> Data t a
abstractD (D x) = x

abstractS :: Callcc t => Stack (Simplifier t) a -> Stack t a
abstractS (S x) = x
