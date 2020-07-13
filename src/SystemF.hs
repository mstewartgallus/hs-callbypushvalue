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

data Inliner t a = I Int (t a)

instance SystemF t => SystemF (Inliner t) where
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
  showb (LabelTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (PairTerm x y) = fromString "(" <> showb x <> fromString ", " <> showb y <> fromString ")"
  showb (FirstTerm tuple) = showb tuple <> fromString ".1"
  showb (SecondTerm tuple) = showb tuple <> fromString ".2"
  showb (LetTerm term binder body) = showb term <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LambdaTerm binder@(Label t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"
  showb (ForallTerm binder@(TypeVariable t _) body) = fromString "∀ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyTypeTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"

simplify :: SystemF t => Term a -> t a
simplify = simp TypeMap.empty LabelMap.empty

simp :: SystemF t => TypeMap Type -> LabelMap t -> Term a -> t a
simp tenv env (PairTerm x y) = pair (simp tenv env x) (simp tenv env y)
simp tenv env (FirstTerm tuple) = first (simp tenv env tuple)
simp tenv env (SecondTerm tuple) = second (simp tenv env tuple)
simp tenv env (ApplyTerm (LambdaTerm binder body) term) =
  let term' = simp tenv env term
   in letBe term' $ \value -> simp tenv (LabelMap.insert binder value env) body
simp tenv env (LetTerm term binder body) =
  let term' = simp tenv env term
   in letBe term' $ \value -> simp tenv (LabelMap.insert binder value env) body
simp tenv env (LambdaTerm binder@(Label t _) body) = lambda t $ \value ->
  simp tenv (LabelMap.insert binder value env) body
simp tenv env (ApplyTerm f x) = apply (simp tenv env f) (simp tenv env x)
simp _ _ (ConstantTerm c) = constant c
simp _ _ (GlobalTerm g) = global g
simp tenv env (ForallTerm binder@(TypeVariable k _) body) = forall k $ \t ->
  simp (TypeMap.insert binder t tenv) env body
simp tenv env (ApplyTypeTerm f x) = SystemF.applyType (simp tenv env f) x
simp _ env (LabelTerm v) = case LabelMap.lookup v env of
  Just x -> x
  Nothing -> error "variable not found in env"

inline :: SystemF t => Term a -> t a
inline term = case inl TypeMap.empty LabelMap.empty term of
  I _ result -> result

data X t a where
  X :: t a -> X t (U a)

inl :: SystemF t => TypeMap Type -> LabelMap t -> Term a -> t a
inl tenv env (PairTerm x y) = pair (inl tenv env x) (inl tenv env y)
inl tenv env (FirstTerm tuple) = first (inl tenv env tuple)
inl tenv env (SecondTerm tuple) = second (inl tenv env tuple)
inl tenv env (LetTerm term binder body) =
  let term' = inl tenv env term
   in if count binder body <= 1
        then inl tenv (LabelMap.insert binder term' env) body
        else letBe term' $ \value ->
          inl tenv (LabelMap.insert binder value env) body
inl _ env (LabelTerm v) = case LabelMap.lookup v env of
  Just x -> x
  Nothing -> error "variable not found in env"
inl tenv env (ApplyTerm f x) = inl tenv env f `apply` inl tenv env x
inl tenv env (LambdaTerm binder@(Label t _) body) = lambda t $ \value ->
  inl tenv (LabelMap.insert binder value env) body
inl _ _ (ConstantTerm c) = constant c
inl _ _ (GlobalTerm g) = global g
inl tenv env (ApplyTypeTerm f x) = inl tenv env f `SystemF.applyType` x
inl tenv env (ForallTerm binder@(TypeVariable t _) body) = forall t $ \value ->
  inl (TypeMap.insert binder value tenv) env body

count :: Label a -> Term b -> Int
count v = w
  where
    w :: Term x -> Int
    w (LabelTerm binder) = if AnyLabel v == AnyLabel binder then 1 else 0
    w (LetTerm term binder body) = w term + w body
    w (LambdaTerm binder body) = w body
    w (ApplyTerm f x) = w f + w x
    w (PairTerm x y) = w x + w y
    w (FirstTerm tuple) = w tuple
    w (SecondTerm tuple) = w tuple
    w _ = 0
