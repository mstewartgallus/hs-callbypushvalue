{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Term (..), Builder (..), simplify, inline, typeOf) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Global
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Type
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

data Term a where
  GlobalTerm :: Global a -> Term a
  ConstantTerm :: Constant a -> Term a
  VariableTerm :: Variable a -> Term a
  LabelTerm :: Label a -> Term (Stack a)
  LetToTerm :: Variable a -> Term R -> Term (Stack (F a))
  PushTerm :: Term a -> Term (Stack b) -> Term (Stack (a :=> b))
  ApplyTerm :: Term (Stack (F a)) -> Term a -> Term R
  PopTerm :: Term (Stack (a :=> b)) -> Label b -> Term (Stack (F a)) -> Term R
  LetBeTerm :: Term a -> Variable a -> Term R -> Term R
  ThunkTerm :: Label a -> Term R -> Term (U a)
  ForceTerm :: Term (U a) -> Term (Stack a) -> Term R

class Cps t where
  constant :: Constant a -> t (Term a)
  global :: Global a -> t (Term a)

  apply :: t (Term (Stack (F a))) -> t (Term a) -> t (Term R)

  thunk :: Action a -> (t (Term (Stack a)) -> t (Term R)) -> t (Term (U a))
  force :: t (Term (U a)) -> t (Term (Stack a)) -> t (Term R)

  letBe :: t (Term a) -> (t (Term a) -> t (Term R)) -> t (Term R)

  pop :: t (Term (Stack (a :=> b))) -> (t (Term (Stack b)) -> t (Term (Stack (F a)))) -> t (Term R)

  nilStack :: t (Term (Stack R))
  letTo :: Type a -> (t (Term a) -> t (Term R)) -> t (Term (Stack (F a)))
  push :: t (Term a) -> t (Term (Stack b)) -> t (Term (Stack (a :=> b)))

instance Cps Builder where
  global g = (Builder . pure) $ GlobalTerm g
  apply k x =
    Builder $
      pure ApplyTerm <*> builder k <*> builder x
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOf x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableTerm v)
    pure $ LetBeTerm x' v body
  pop x f = Builder $ do
    x' <- builder x
    let StackType (a :=> b) = typeOf x'
    t <- pure (Label b) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) (LabelTerm t))
    pure $ PopTerm x' t body
  constant k = (Builder . pure) $ ConstantTerm k

  letTo t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableTerm v))
    pure $ LetToTerm v body

  thunk t f = Builder $ do
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ LabelTerm v))
    pure $ ThunkTerm v body

  force thnk stk =
    Builder $
      pure ForceTerm <*> builder thnk <*> builder stk

  push x k = Builder $ do
    pure PushTerm <*> builder x <*> builder k

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (LabelTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm k) = showb k
  showb (LetBeTerm value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LetToTerm binder@(Variable t _) body) =
    fromString "to " <> showb binder <> fromString ": " <> showb t <> fromString ".\n" <> showb body
  showb (PopTerm value t body) =
    showb t <> fromString ":\n"
      <> fromString "pop "
      <> showb value
      <> fromString ".\n"
      <> showb body
  showb (PushTerm x f) = showb x <> fromString " :: " <> showb f
  showb (ThunkTerm binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " " <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body)))
  showb (ApplyTerm k x) = fromString "jump " <> showb k <> fromString " " <> showb x
  showb (ForceTerm thnk stk) = fromString "! " <> showb thnk <> fromString " " <> showb stk

build :: Builder a -> a
build (Builder s) = Unique.run s

newtype Builder a = Builder {builder :: Unique.State a}

typeOf :: Term a -> Type a
typeOf (GlobalTerm (Global t _)) = t
typeOf (ConstantTerm k) = Constant.typeOf k
typeOf (ThunkTerm (Label t _) _) = U t
typeOf (VariableTerm (Variable t _)) = t
typeOf (LabelTerm (Label t _)) = StackType t
typeOf (LetToTerm (Variable t _) _) = StackType (F t)
typeOf (PushTerm h t) =
  let a = typeOf h
      StackType b = typeOf t
   in StackType (a :=> b)

simplify :: Term a -> Term a
simplify (ForceTerm f x) = ForceTerm (simplify f) (simplify x)
simplify (ThunkTerm binder body) = ThunkTerm binder (simplify body)
simplify (LetToTerm binder body) = LetToTerm binder (simplify body)
simplify (PushTerm h t) = PushTerm (simplify h) (simplify t)
simplify (PopTerm value t body) = PopTerm (simplify value) t (simplify body)
simplify (LetBeTerm thing binder body) = LetBeTerm (simplify thing) binder (simplify body)
simplify (ApplyTerm k x) = ApplyTerm (simplify k) (simplify x)
simplify x = x

inline :: Cps t => Term a -> t (Term a)
inline = inline' LabelMap.empty VarMap.empty

newtype X t a = X (t (Term a))

newtype L t a = L (t (Term (Stack a)))

inline' :: Cps t => LabelMap (L t) -> VarMap (X t) -> Term a -> t (Term a)
inline' _ env (VariableTerm v) =
  let Just (X x) = VarMap.lookup v env
   in x
inline' lenv _ (LabelTerm v) =
  let Just (L x) = LabelMap.lookup v lenv
   in x
inline' lenv env (LetToTerm binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in inline' lenv env' body
inline' lenv env (PushTerm h t) = Cps.push (inline' lenv env h) (inline' lenv env t)
inline' _ _ (ConstantTerm k) = Cps.constant k
inline' _ _ (GlobalTerm g) = global g
inline' lenv env (LetBeTerm term binder body)
  | count binder body <= 1 || isSimple term =
    let term' = inline' lenv env term
     in inline' lenv (VarMap.insert binder (X term') env) body
  | otherwise = letBe (inline' lenv env term) $ \x ->
    inline' lenv (VarMap.insert binder (X x) env) body
inline' lenv env (PopTerm value t body) = pop (inline' lenv env value) $ \y ->
  inline' (LabelMap.insert t (L y) lenv) env body
inline' lenv env (ApplyTerm k x) = apply (inline' lenv env k) (inline' lenv env x)
inline' lenv env (ForceTerm k x) = force (inline' lenv env k) (inline' lenv env x)
inline' lenv env (ThunkTerm binder@(Label t _) body) = thunk t $ \k ->
  inline' (LabelMap.insert binder (L k) lenv) env body

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple (VariableTerm _) = True
isSimple (LabelTerm _) = True
isSimple (GlobalTerm _) = True
isSimple _ = False

count :: Variable a -> Term b -> Int
count v = w
  where
    w :: Term b -> Int
    w (LetBeTerm x binder body) = w x + if AnyVariable binder == AnyVariable v then 0 else w body
    w (PopTerm x t body) = w x + w body
    w (ApplyTerm k x) = w k + w x
    w (LetToTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else w body
    w (PushTerm h t) = w h + w t
    w (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    w _ = 0
