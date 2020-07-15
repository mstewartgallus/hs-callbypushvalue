{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, simplify, inline, build, Builder, SystemF (..), abstract, Term (..)) where

import Common
import Constant (Constant)
import qualified Constant
import Core hiding (minus, plus)
import qualified Core
import qualified Data.Text as T
import Global
import Kind
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import TextShow (TextShow, fromString, showb)
import qualified TextShow (Builder)
import Type
import qualified Unique
import View
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class SystemF (t :: forall k. k -> *) where
  -- | function application
  (<*>) :: t (a :-> b) -> t a -> t b

  -- |
  --
  -- FIXME find a way to unify constant and lambda into a sort of
  -- pure equivalent
  constant ::
    forall (a :: Set).
    Constant a ->
    t (F a)

  lambda ::
    forall (a :: Alg) (b :: Alg).
    SAlg a ->
    (t a -> t b) ->
    t (a :-> b)

  global ::
    forall (a :: Alg).
    Global a ->
    t a

  letBe ::
    forall (a :: Alg) (b :: Alg).
    t a ->
    (t a -> t b) ->
    t b

  pair :: t a -> t b -> t (Pair a b)
  unpair ::
    forall a b (c :: Alg).
    t (Pair a b) ->
    (t a -> t b -> t c) ->
    t c

lam :: forall (t :: forall k. k -> *) a b. (SystemF t, KnownAlg a) => (t a -> t b) -> t (a :-> b)
lam = lambda inferAlg

-- forall :: Kind a -> (Type a -> t b) -> t (V a b)
-- applyType :: t (V a b) -> Type a -> t b

infixl 4 <*>

-- | Tagless final newtype to inline letBe clauses based on a simple
-- cost model
--
-- FIXME: for now all the node costs and inline thresholds are
-- arbitrary and will need tuning
--
-- FIXME: use an alternative to the probe function
data CostInliner (a :: k) = I Int (Builder a)

instance SystemF CostInliner where
  constant k = I 0 (constant k)
  global g = I 0 (global g)

  pair (I xcost x) (I ycost y) = I (xcost + ycost + 1) (pair x y)

  letBe (I xcost x) f = result
    where
      result
        | xcost <= 3 = inlined
        | otherwise = notinlined
      inlined@(I fcost _) = f (I 0 x)
      notinlined = I (xcost + fcost + 1) $ letBe x $ \x' -> case f (I 0 x') of
        I _ y -> y

  lambda t f = result
    where
      I fcost _ = f (I 0 (global (probe t)))
      result = I (fcost + 1) $ lambda t $ \x' -> case f (I 0 x') of
        I _ y -> y
  I fcost f <*> I xcost x = I (fcost + xcost + 1) (f <*> x)

data MonoInliner (a :: k) = M Int (Builder a)

instance SystemF MonoInliner where
  constant k = M 0 (constant k)
  global g = M 0 (global g)

  pair (M xcost x) (M ycost y) = M (xcost + ycost) (pair x y)

  letBe (M xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(M inlineCost _) = f (M 1 x)
      notinlined = M (xcost + fcost) $ letBe x $ \x' -> case f (M 0 x') of
        M _ y -> y
      M fcost _ = f (M 0 x)

  lambda t f =
    let M fcost _ = f (M 0 (global (probe t)))
     in M fcost $ lambda t $ \x' -> case f (M 0 x') of
          M _ y -> y
  M fcost f <*> M xcost x = M (fcost + xcost) (f <*> x)

probe :: SAlg a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")

data Term a where
  LabelTerm :: Label a -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Label a -> Term b -> Term b
  LambdaTerm :: Label a -> Term b -> Term (a :-> b)
  PairTerm :: Term a -> Term b -> Term (Pair a b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

abstract :: forall (t :: forall k. k -> *) a. SystemF t => Term a -> t a
abstract = abstract' LabelMap.empty

abstract' :: forall (t :: forall k. k -> *) a. SystemF t => LabelMap t -> Term a -> t a
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

instance TextShow (Term a) where
  showb = showTerm

showTerm :: forall a. Term a -> TextShow.Builder
showTerm term = case abstract term of
  V b -> Unique.withStream b

instance SystemF View where
  constant k = V $ \_ -> showb k
  global g = V $ \_ -> showb g
  pair (V x) (V y) = V $ \(Unique.Stream _ xs ys) ->
    let x' = x xs
        y' = y ys
     in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"

  letBe (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = V $ \(Unique.Stream newId _ ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ".\n" <> y ys

  V f <*> V x = V $ \(Unique.Stream _ fs xs) ->
    fromString "(" <> f fs <> fromString " " <> x xs <> fromString ")"

simplify :: forall (t :: forall k. k -> *) a. SystemF t => Term a -> t a
simplify term = case abstract term of
  S _ x -> abstract (build x)

data Simplifier (a :: k) = S (MaybeFn a) (Builder a)

data MaybeFn (a :: k) where
  Fn :: (Builder a -> Builder b) -> MaybeFn (a :-> b)
  NotFn :: MaybeFn a

instance SystemF Simplifier where
  constant k = S NotFn (constant k)
  global g = S NotFn (global g)

  pair (S _ x) (S _ y) = S NotFn (pair x y)

  letBe (S _ x) f = S NotFn $ letBe x $ \x' -> case f (S NotFn x') of
    S _ y -> y

  lambda t f =
    let f' x' = case f (S NotFn x') of
          S _ y -> y
     in S (Fn f') $ lambda t f'

  S NotFn f <*> S _ x = S NotFn (f <*> x)
  S (Fn f) _ <*> S _ x = S NotFn (letBe x f)

inline :: Term a -> Term a
inline term = costInline (monoInline term)

monoInline :: Term a -> Term a
monoInline term = case abstract term of
  M _ m -> build m

costInline :: Term a -> Term a
costInline term = case abstract term of
  I _ x -> build x

data family Builder (a :: k)

newtype instance Builder (a :: Alg) = B (forall s. Unique.Stream s -> (SAlg a, Term a))

build :: Builder a -> Term a
build (B f) =
  let (_, x) = Unique.withStream f
   in x

instance SystemF Builder where
  constant k = B $ \_ -> (SF (Constant.typeOf k), ConstantTerm k)
  global g@(Global t _) = B $ \_ -> (t, GlobalTerm g)
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
