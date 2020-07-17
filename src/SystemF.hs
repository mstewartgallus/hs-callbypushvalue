{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, simplify, Simplifier, box, SystemF (..), interpret, Term) where

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
import HasReturn
import Name
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class (HasGlobals t, HasConstants t, HasReturn t) => SystemF t where
  -- | function application
  (<*>) :: CodeRep t (a :-> b) -> CodeRep t a -> CodeRep t b

  lambda :: SAlgebra a -> (CodeRep t a -> CodeRep t b) -> CodeRep t (a :-> b)

  letBe :: CodeRep t a -> (CodeRep t a -> CodeRep t b) -> CodeRep t b

  pair :: CodeRep t a -> CodeRep t b -> CodeRep t (Pair a b)
  unpair ::
    CodeRep t (Pair a b) ->
    (CodeRep t a -> CodeRep t b -> CodeRep t c) ->
    CodeRep t c

lam :: (SystemF t, KnownAlgebra a) => (CodeRep t a -> CodeRep t b) -> CodeRep t (a :-> b)
lam = lambda inferAlgebra

infixl 4 <*>

newtype Term a = Term (forall t. SystemF t => CodeRep t a)

interpret :: SystemF t => Term a -> CodeRep t a
interpret (Term x) = x

simplify :: SystemF t => CodeRep (Simplifier t) a -> CodeRep t a
simplify (S _ x) = x

data Simplifier t

data MaybeFn t a where
  Fn :: (CodeRep t a -> CodeRep t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance HasCode t => HasCode (Simplifier t) where
  data CodeRep (Simplifier t) a = S (MaybeFn t a) (CodeRep t a)

instance HasData t => HasData (Simplifier t) where
  newtype DataRep (Simplifier t) a = SS (DataRep t a)

instance HasGlobals t => HasGlobals (Simplifier t) where
  global g = S NotFn (global g)

instance HasConstants t => HasConstants (Simplifier t) where
  constant k = SS (constant k)
  unit = SS unit

instance HasReturn t => HasReturn (Simplifier t) where
  returns (SS k) = S NotFn (returns k)

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

box :: (forall t. SystemF t => CodeRep t a) -> Term a
box = Term
