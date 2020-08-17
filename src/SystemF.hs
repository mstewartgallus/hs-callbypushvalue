{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, SystemF, HasLet (..), HasTuple (..), HasFn (..), HasConstants (..)) where

import Common
import Constant
import HasCall
import HasCode
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- This is kind of like an applicative functor as compared to call by
-- push value which is more like a monad (it is literally based on
-- adjoint functors.)
--
-- FIXME: forall and applyType are not yet implemented
type SystemF t = (HasCode t, HasCall t, HasConstants t, HasFn t, HasLet t, HasTuple t)

class HasCode t => HasLet t where
  letBe :: Code t a -> (Code t a -> Code t b) -> Code t b
  letBe = flip whereIs

  whereIs :: (Code t a -> Code t b) -> Code t a -> Code t b
  whereIs = flip letBe

class HasCode t => HasConstants t where
  constant :: Constant a -> Code t (F a)

class HasCode t => HasTuple t where
  -- | factorizer from category theory
  pair :: (Code t a -> Code t b) -> (Code t a -> Code t c) -> (Code t a -> Code t (Pair b c))

  first :: Code t (Pair a b) -> Code t a
  second :: Code t (Pair a b) -> Code t b

class HasCode t => HasFn t where
  (<*>) :: Code t (a --> b) -> Code t a -> Code t b
  lambda :: SAlgebra a -> (Code t a -> Code t b) -> Code t (a --> b)

  uncurry :: (Code t a -> Code t (b --> c)) -> (Code t (Pair a b) -> Code t c)
  curry :: (Code t (Pair a b) -> Code t c) -> (Code t a -> Code t (b --> c))

infixl 4 <*>

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (HasFn t, KnownAlgebra a) => (Code t a -> Code t b) -> Code t (a --> b)
lam = lambda inferAlgebra
