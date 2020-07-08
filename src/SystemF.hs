{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (simplify, inline, build, Builder, SystemF (..), Term (..)) where

import Common
import Constant
import Core
import Global
import Kind
import TextShow (TextShow, fromString, showb)
import Type
import TypeMap (TypeMap)
import qualified TypeMap
import TypeVariable
import qualified Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

class SystemF t where
  constant :: Constant a -> t Term (F a)
  global :: Global a -> t Term a
  lambda :: Type a -> (t Term a -> t Term b) -> t Term (a :-> b)
  apply :: t Term (a :-> b) -> t Term a -> t Term b
  letBe :: t Term a -> (t Term a -> t Term b) -> t Term b

  forall :: Kind a -> (Type a -> t Term b) -> t Term (V a b)
  applyType :: t Term (V a b) -> Type a -> t Term b

newtype Builder t a = Builder {builder :: Unique.State (t a)}

build :: Builder t a -> t a
build (Builder s) = Unique.run s

instance SystemF Builder where
  constant k = (Builder . pure) $ ConstantTerm k
  global g = (Builder . pure) $ GlobalTerm g
  letBe value f = Builder $ do
    value' <- builder value
    let t = typeOf value'
    binder <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f (Builder $ pure $ VariableTerm binder)
    pure (LetTerm value' binder body)
  lambda t f = Builder $ do
    binder <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f (Builder $ pure $ VariableTerm binder)
    pure (LambdaTerm binder body)
  forall t f = Builder $ do
    binder <- pure (TypeVariable t) <*> Unique.uniqueId
    body <- builder $ f (VariableType binder)
    pure (ForallTerm binder body)
  apply f x =
    Builder $
      pure ApplyTerm <*> builder f <*> builder x
  applyType f x = Builder $ do
    f' <- builder f
    pure (ApplyTypeTerm f' x)

data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Variable a -> Term b -> Term b
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ForallTerm :: TypeVariable a -> Term b -> Term (V a b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b
  ApplyTypeTerm :: Term (V a b) -> Type a -> Term b

typeOf :: Term a -> Type a
typeOf (VariableTerm (Variable t _)) = t
typeOf (ConstantTerm (IntegerConstant _)) = int
typeOf (GlobalTerm (Global t _)) = t
typeOf (LetTerm _ _ body) = typeOf body
typeOf (LambdaTerm (Variable t _) body) = t -#-> typeOf body
typeOf (ApplyTerm f _) =
  let _ :=> result = typeOf f
   in result
typeOf (ForallTerm _ _) = undefined
typeOf (ApplyTypeTerm _ _) = undefined

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = showb term <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LambdaTerm binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"
  showb (ForallTerm binder@(TypeVariable t _) body) = fromString "∀ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyTypeTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"

simplify :: SystemF t => Term a -> t Term a
simplify = simp TypeMap.empty VarMap.empty

simp :: SystemF t => TypeMap Type -> VarMap (t Term) -> Term a -> t Term a
simp tenv env (ApplyTerm (LambdaTerm binder body) term) =
  let term' = simp tenv env term
   in letBe term' $ \value -> simp tenv (VarMap.insert binder value env) body
simp tenv env (LetTerm term binder body) =
  let term' = simp tenv env term
   in letBe term' $ \value -> simp tenv (VarMap.insert binder value env) body
simp tenv env (LambdaTerm binder@(Variable t _) body) = lambda t $ \value ->
  simp tenv (VarMap.insert binder value env) body
simp tenv env (ApplyTerm f x) = apply (simp tenv env f) (simp tenv env x)
simp _ _ (ConstantTerm c) = constant c
simp _ _ (GlobalTerm g) = global g
simp tenv env (ForallTerm binder@(TypeVariable k _) body) = forall k $ \t ->
  simp (TypeMap.insert binder t tenv) env body
simp tenv env (ApplyTypeTerm f x) = SystemF.applyType (simp tenv env f) x
simp _ env (VariableTerm v) = case VarMap.lookup v env of
  Just x -> x
  Nothing -> error "variable not found in env"

count :: Variable a -> Term b -> Int
count v = w
  where
    w :: Term x -> Int
    w (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    w (LetTerm term binder body) = w term + if AnyVariable binder == AnyVariable v then 0 else w body
    w (LambdaTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else w body
    w (ApplyTerm f x) = w f + w x
    w _ = 0

inline :: SystemF t => Term a -> t Term a
inline = inl TypeMap.empty VarMap.empty

inl :: SystemF t => TypeMap Type -> VarMap (t Term) -> Term a -> t Term a
inl tenv env (LetTerm term binder body) =
  let term' = inl tenv env term
   in if count binder body <= 1 || isSimple term
        then inl tenv (VarMap.insert binder term' env) body
        else letBe term' $ \value ->
          inl tenv (VarMap.insert binder value env) body
inl _ env (VariableTerm v) = case VarMap.lookup v env of
  Just replacement -> replacement
  Nothing -> error "variable not found in env"
inl tenv env (ApplyTerm f x) = inl tenv env f `apply` inl tenv env x
inl tenv env (LambdaTerm binder@(Variable t _) body) = lambda t $ \value ->
  inl tenv (VarMap.insert binder value env) body
inl _ _ (ConstantTerm c) = constant c
inl _ _ (GlobalTerm g) = global g
inl tenv env (ApplyTypeTerm f x) = inl tenv env f `SystemF.applyType` x
inl tenv env (ForallTerm binder@(TypeVariable t _) body) = forall t $ \value ->
  inl (TypeMap.insert binder value tenv) env body

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple _ = False
