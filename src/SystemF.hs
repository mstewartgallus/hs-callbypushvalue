{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, simplify, Simplifier, build, Builder, SystemF (..), abstract, Term (..)) where

import Basic
import Common
import Constant (Constant)
import qualified Constant
import Core hiding (minus, plus)
import qualified Core
import Global
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import qualified Unique
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class Basic t => SystemF t where
  -- | function application
  (<*>) :: AlgRep t (a :-> b) -> AlgRep t a -> AlgRep t b

  -- |
  --
  -- FIXME find a way to unify constant and lambda into a sort of
  -- pure equivalent
  constant :: Constant a -> AlgRep t (F a)

  lambda :: SAlg a -> (AlgRep t a -> AlgRep t b) -> AlgRep t (a :-> b)

  letBe :: AlgRep t a -> (AlgRep t a -> AlgRep t b) -> AlgRep t b

  pair :: AlgRep t a -> AlgRep t b -> AlgRep t (Pair a b)
  unpair ::
    AlgRep t (Pair a b) ->
    (AlgRep t a -> AlgRep t b -> AlgRep t c) ->
    AlgRep t c

lam :: (SystemF t, KnownAlg a) => (AlgRep t a -> AlgRep t b) -> AlgRep t (a :-> b)
lam = lambda inferAlg

-- forall :: Kind a -> (Type a -> t b) -> t (V a b)
-- applyType :: t (V a b) -> Type a -> t b

infixl 4 <*>

data Term a where
  LabelTerm :: Label a -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Label a -> Term b -> Term b
  LambdaTerm :: Label a -> Term b -> Term (a :-> b)
  PairTerm :: Term a -> Term b -> Term (Pair a b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

abstract :: SystemF t => Term a -> AlgRep t a
abstract = abstract' LabelMap.empty

abstract' :: SystemF t => LabelMap (AlgRep t) -> Term a -> AlgRep t a
abstract' env term = case term of
  PairTerm x y -> pair (abstract' env x) (abstract' env y)
  LetTerm term binder body ->
    let term' = abstract' env term
     in letBe term' $ \value -> abstract' (LabelMap.insert binder value env) body
  LambdaTerm binder@(Label t _) body -> lambda t $ \value ->
    abstract' (LabelMap.insert binder value env) body
  ApplyTerm f x -> abstract' env f <*> abstract' env x
  ConstantTerm c -> constant c
  GlobalTerm g -> global g
  LabelTerm v -> case LabelMap.lookup v env of
    Just x -> x
    Nothing -> error "variable not found in env"

simplify :: SystemF t => AlgRep (Simplifier t) a -> AlgRep t a
simplify (S _ x) = x

data Simplifier t

data MaybeFn t a where
  Fn :: (AlgRep t a -> AlgRep t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance Basic t => Basic (Simplifier t) where
  data AlgRep (Simplifier t) a = S (MaybeFn t a) (AlgRep t a)
  global g = S NotFn (global g)

instance SystemF t => SystemF (Simplifier t) where
  constant k = S NotFn (constant k)

  pair (S _ x) (S _ y) = S NotFn (pair x y)

  letBe (S _ x) f = S NotFn $ letBe x $ \x' -> case f (S NotFn x') of
    S _ y -> y

  lambda t f =
    let f' x' = case f (S NotFn x') of
          S _ y -> y
     in S (Fn f') $ lambda t f'

  S NotFn f <*> S _ x = S NotFn (f <*> x)
  S (Fn f) _ <*> S _ x = S NotFn (letBe x f)

data Builder

build :: AlgRep Builder a -> Term a
build (B f) =
  let (_, x) = Unique.withStream f
   in x

instance Basic Builder where
  newtype AlgRep Builder (a :: Alg) = B (forall s. Unique.Stream s -> (SAlg a, Term a))
  global g@(Global t _) = B $ \_ -> (t, GlobalTerm g)

instance SystemF Builder where
  constant k = B $ \_ -> (SF (Constant.typeOf k), ConstantTerm k)

  pair (B x) (B y) = B $ \(Unique.Stream _ xs ys) ->
    let (tx, vx) = x xs
        (ty, vy) = y ys
     in (SF (SU tx `SPair` SU ty), PairTerm vx vy)
  letBe (B x) f = B $ \(Unique.Stream newId xs fs) ->
    let (tx, vx) = x xs
        binder = Label tx newId
        B b = f (B $ \_ -> (tx, LabelTerm binder))
        (result, body) = b fs
     in (result, LetTerm vx binder body)
  lambda t f = B $ \(Unique.Stream newId _ tail) ->
    let binder = Label t newId
        B b = f (B $ \_ -> (t, LabelTerm binder))
        (result, body) = b tail
     in (SU t `SFn` result, LambdaTerm binder body)
  B f <*> B x = B $ \(Unique.Stream _ fs xs) ->
    let (SFn _ b, vf) = f fs
        (_, vx) = x xs
     in (b, ApplyTerm vf vx)
