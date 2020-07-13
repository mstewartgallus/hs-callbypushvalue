{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (simplify, inline, build, Builder, SystemF (..), minus, plus, abstract, Term (..)) where

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
import TypeMap (TypeMap)
import qualified TypeMap
import TypeVariable
import qualified Unique

class SystemF t where
  constant :: Constant a -> t (F a)

  global :: Global a -> t a

  lambda :: Action a -> (t a -> t b) -> t (a :-> b)
  apply :: t (a :-> b) -> t a -> t b
  letBe :: t a -> (t a -> t b) -> t b

  pair :: t a -> t b -> t (Pair a b)
  first :: t (Pair a b) -> t a
  second :: t (Pair a b) -> t b

  forall :: Kind a -> (Type a -> t b) -> t (V a b)
  applyType :: t (V a b) -> Type a -> t b

plus :: SystemF t => t (F Integer) -> t (F Integer) -> t (F Integer)
plus x y = apply (apply (global Core.plus) x) y

minus :: SystemF t => t (F Integer) -> t (F Integer) -> t (F Integer)
minus x y = apply (apply (global Core.minus) x) y

data CostInliner t a = I Int (t a)

instance SystemF t => SystemF (CostInliner t) where
  constant k = I 0 (constant k)
  global g = I 0 (global g)

  pair (I xcost x) (I ycost y) = I (xcost + ycost + 1) (pair x y)

  letBe (I xcost x) f = result
    where
      inlined@(I fcost _) = f (I 0 x)
      notinlined =
        I
          (xcost + fcost + 1)
          ( letBe x $ \x' -> case f (I 0 x') of
              I _ y -> y
          )
      -- FIXME: for now all the cost and inline thresholds are
      -- arbitrary and will need tuning
      result
        | xcost <= 3 = inlined
        | otherwise = notinlined

  lambda t f = result
    where
      I fcost _ = f (I 0 (global (probe t)))
      result = I (fcost + 1) $ lambda t $ \x' -> case f (I 0 x') of
        I _ y -> y
  apply (I fcost f) (I xcost x) = I (fcost + xcost + 1) (apply f x)

-- | Basically the same as Cost inliner but only measures how often a
-- variable occurs.  Everytime we make this check we make a probe with
-- Mono 1 in letBe.  Nothing else should add a constant amount.
data Mono t a = Mono Int (t a)

instance SystemF t => SystemF (Mono t) where
  constant k = Mono 0 (constant k)
  global g = Mono 0 (global g)

  pair (Mono xcost x) (Mono ycost y) = Mono (xcost + ycost) (pair x y)

  letBe (Mono xcost x) f = result
    where
      inlined@(Mono inlineCost _) = f (Mono 1 x)
      Mono fcost _ = f (Mono 0 x)
      notinlined =
        Mono
          (xcost + fcost)
          ( letBe x $ \x' -> case f (Mono 0 x') of
              Mono _ y -> y
          )
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined

  lambda t f =
    let Mono fcost _ = f (Mono 0 (global (probe t)))
     in Mono fcost $ lambda t $ \x' -> case f (Mono 0 x') of
          Mono _ y -> y
  apply (Mono fcost f) (Mono xcost x) = Mono (fcost + xcost) (apply f x)

probe :: Action a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")

data Term a where
  LabelTerm :: Label a -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Label a -> Term b -> Term b
  LambdaTerm :: Label a -> Term b -> Term (a :-> b)
  ForallTerm :: TypeVariable a -> Term b -> Term (V a b)
  PairTerm :: Term a -> Term b -> Term (Pair a b)
  FirstTerm :: Term (Pair a b) -> Term a
  SecondTerm :: Term (Pair a b) -> Term b
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b
  ApplyTypeTerm :: Term (V a b) -> Type a -> Term b

abstract :: SystemF t => Term a -> t a
abstract = abstract' TypeMap.empty LabelMap.empty

abstract' :: SystemF t => TypeMap Type -> LabelMap t -> Term a -> t a
abstract' tenv env (PairTerm x y) = pair (abstract' tenv env x) (abstract' tenv env y)
abstract' tenv env (FirstTerm tuple) = first (abstract' tenv env tuple)
abstract' tenv env (SecondTerm tuple) = second (abstract' tenv env tuple)
abstract' tenv env (LetTerm term binder body) =
  let term' = abstract' tenv env term
   in letBe term' $ \value -> abstract' tenv (LabelMap.insert binder value env) body
abstract' tenv env (LambdaTerm binder@(Label t _) body) = lambda t $ \value ->
  abstract' tenv (LabelMap.insert binder value env) body
abstract' tenv env (ApplyTerm f x) = apply (abstract' tenv env f) (abstract' tenv env x)
abstract' _ _ (ConstantTerm c) = constant c
abstract' _ _ (GlobalTerm g) = global g
abstract' tenv env (ForallTerm binder@(TypeVariable k _) body) = forall k $ \t ->
  abstract' (TypeMap.insert binder t tenv) env body
abstract' tenv env (ApplyTypeTerm f x) = SystemF.applyType (abstract' tenv env f) x
abstract' _ env (LabelTerm v) = case LabelMap.lookup v env of
  Just x -> x
  Nothing -> error "variable not found in env"

instance TextShow (Term a) where
  showb term = case abstract term of
    V b -> Unique.withStream b

newtype View a = V (forall s. Unique.Stream s -> TextShow.Builder)

instance SystemF View where
  constant k = V $ \_ -> showb k
  global g = V $ \_ -> showb g
  pair (V x) (V y) = V $ \(Unique.Stream _ xs ys) ->
    let x' = x xs
        y' = y ys
     in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"
  first (V tuple) = V $ \s -> tuple s <> fromString ".1"
  second (V tuple) = V $ \s -> tuple s <> fromString ".2"

  letBe (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = V $ \(Unique.Stream newId _ ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ".\n" <> y ys

  apply (V f) (V x) = V $ \(Unique.Stream _ fs xs) ->
    fromString "(" <> f fs <> fromString " " <> x xs <> fromString ")"

simplify :: SystemF t => Term a -> t a
simplify term = case abstract term of
  S _ x -> x

data Simplifier t a = S (MaybeFn t a) (t a)

data MaybeFn t a where
  Fn :: (t a -> t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance SystemF t => SystemF (Simplifier t) where
  constant k = S NotFn (constant k)
  global g = S NotFn (global g)

  pair (S _ x) (S _ y) = S NotFn (pair x y)

  letBe (S _ x) f = S NotFn $ letBe x $ \x' -> case f (S NotFn x') of
    S _ y -> y

  lambda t f =
    let f' x' = case f (S NotFn x') of
          S _ y -> y
     in S (Fn f') $ lambda t f'
  apply (S NotFn f) (S _ x) = S NotFn (apply f x)
  apply (S (Fn f) _) (S _ x) = S NotFn (letBe x f)

inline :: SystemF t => Term a -> t a
inline term = case abstract term of
  Mono _ (I _ result) -> result

newtype Builder a = B (forall s. Unique.Stream s -> (Action a, Term a))

build :: Builder a -> Term a
build (B f) =
  let (_, x) = Unique.withStream f
   in x

instance SystemF Builder where
  constant k = B $ \_ -> (F (Constant.typeOf k), ConstantTerm k)
  global g@(Global t _) = B $ \_ -> (t, GlobalTerm g)
  pair (B x) (B y) = B $ \(Unique.Stream _ xs ys) ->
    let (tx, vx) = x xs
        (ty, vy) = y ys
     in (F (U tx :*: U ty :*: UnitType), PairTerm vx vy)
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
     in (U t :=> result, LambdaTerm binder body)
  apply (B f) (B x) = B $ \(Unique.Stream _ fs xs) ->
    let (_ :=> b, vf) = f fs
        (_, vx) = x xs
     in (b, ApplyTerm vf vx)
