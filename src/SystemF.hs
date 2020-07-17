{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, simplify, Simplifier, build, SystemF (..), abstract, Term (..)) where

import Common
import Constant (Constant)
import qualified Constant
import Core hiding (minus, plus)
import qualified Core
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import Name
import qualified Pure
import qualified Unique
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class (HasGlobals t, HasConstants t, Pure.Pure t) => SystemF t where
  -- | function application
  (<*>) :: AlgRep t (a :-> b) -> AlgRep t a -> AlgRep t b

  lambda :: SAlgebra a -> (AlgRep t a -> AlgRep t b) -> AlgRep t (a :-> b)

  letBe :: AlgRep t a -> (AlgRep t a -> AlgRep t b) -> AlgRep t b

  pair :: AlgRep t a -> AlgRep t b -> AlgRep t (Pair a b)
  unpair ::
    AlgRep t (Pair a b) ->
    (AlgRep t a -> AlgRep t b -> AlgRep t c) ->
    AlgRep t c

lam :: (SystemF t, KnownAlgebra a) => (AlgRep t a -> AlgRep t b) -> AlgRep t (a :-> b)
lam = lambda inferAlgebra

infixl 4 <*>

newtype Term a = Term (forall t. SystemF t => AlgRep t a)

abstract :: SystemF t => Term a -> AlgRep t a
abstract (Term x) = x

simplify :: SystemF t => AlgRep (Simplifier t) a -> AlgRep t a
simplify (S _ x) = x

data Simplifier t

data MaybeFn t a where
  Fn :: (AlgRep t a -> AlgRep t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance HasCode t => HasCode (Simplifier t) where
  data AlgRep (Simplifier t) a = S (MaybeFn t a) (AlgRep t a)

instance HasData t => HasData (Simplifier t) where
  newtype SetRep (Simplifier t) a = SS (SetRep t a)

instance HasGlobals t => HasGlobals (Simplifier t) where
  global g = S NotFn (global g)

instance HasConstants t => HasConstants (Simplifier t) where
  constant k = SS (constant k)
  unit = SS unit

instance Pure.Pure t => Pure.Pure (Simplifier t) where
  pure (SS k) = S NotFn (Pure.pure k)

instance SystemF t => SystemF (Simplifier t) where
  pair (S _ x) (S _ y) = S NotFn (pair x y)

  letBe (S _ x) f = S NotFn $ letBe x $ \x' -> case f (S NotFn x') of
    S _ y -> y

  lambda t f =
    let f' x' = case f (S NotFn x') of
          S _ y -> y
     in S (Fn f') $ lambda t f'

  S NotFn f <*> S _ x = S NotFn (f <*> x)
  S (Fn f) _ <*> S _ x = S NotFn (letBe x f)

build :: (forall t. SystemF t => AlgRep t a) -> Term a
build = Term
