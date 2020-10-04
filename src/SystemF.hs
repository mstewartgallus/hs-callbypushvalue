{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module SystemF (lam, SystemF, HasCall (..), HasLet (..), HasTuple (..), HasFn (..), HasConstants (..)) where

import Constant
import Global
import HasTerm
import SystemF.Type
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- This is kind of like an applicative functor as compared to call by
-- push value which is more like a monad (it is literally based on
-- adjoint functors.)
--
-- FIXME: forall and applyType are not yet implemented
type SystemF t = (HasTerm t, HasCall t, HasConstants t, HasFn t, HasLet t, HasTuple t)

class HasTerm t => HasLet t where
  letBe :: Term t a -> (Term t a -> Term t b) -> Term t b
  letBe = flip whereIs

  whereIs :: (Term t a -> Term t b) -> Term t a -> Term t b
  whereIs = flip letBe

class HasTerm t => HasConstants t where
  constant :: Constant a -> Term t a

class HasTerm t => HasCall t where
  call :: Global a -> Term t a

class HasTerm t => HasTuple t where
  -- | factorizer from category theory
  pair :: (Term t a -> Term t b) -> (Term t a -> Term t c) -> (Term t a -> Term t (b * c))

  first :: Term t (a * b) -> Term t a
  second :: Term t (a * b) -> Term t b

class HasTerm t => HasFn t where
  (<*>) :: Term t (a ~> b) -> Term t a -> Term t b
  lambda :: SType a -> (Term t a -> Term t b) -> Term t (a ~> b)

  uncurry :: (Term t a -> Term t (b ~> c)) -> (Term t (a * b) -> Term t c)
  curry :: (Term t (a * b) -> Term t c) -> (Term t a -> Term t (b ~> c))

infixl 4 <*>

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (HasFn t, KnownType a) => (Term t a -> Term t b) -> Term t (a ~> b)
lam = lambda inferType
