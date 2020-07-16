{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, simplify, Simplifier, build, SystemF (..), abstract, Term (..)) where

import Basic
import Common
import Const
import Constant (Constant)
import qualified Constant
import Core hiding (minus, plus)
import qualified Core
import Global
import Name
import qualified Unique
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class (Basic t, Const t) => SystemF t where
  -- | function application
  (<*>) :: AlgRep t (a :-> b) -> AlgRep t a -> AlgRep t b

  constant :: SetRep t a -> AlgRep t (F a)

  lambda :: SAlg a -> (AlgRep t a -> AlgRep t b) -> AlgRep t (a :-> b)

  letBe :: AlgRep t a -> (AlgRep t a -> AlgRep t b) -> AlgRep t b

  pair :: AlgRep t a -> AlgRep t b -> AlgRep t (Pair a b)
  unpair ::
    AlgRep t (Pair a b) ->
    (AlgRep t a -> AlgRep t b -> AlgRep t c) ->
    AlgRep t c

lam :: (SystemF t, KnownAlg a) => (AlgRep t a -> AlgRep t b) -> AlgRep t (a :-> b)
lam = lambda inferAlg

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

instance Basic t => Basic (Simplifier t) where
  data AlgRep (Simplifier t) a = S (MaybeFn t a) (AlgRep t a)
  global g = S NotFn (global g)

instance Const t => Const (Simplifier t) where
  newtype SetRep (Simplifier t) a = SS (SetRep t a)
  unit = SS unit

instance SystemF t => SystemF (Simplifier t) where
  constant (SS k) = S NotFn (SystemF.constant k)

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
