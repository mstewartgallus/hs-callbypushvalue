{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (simplify, inline, build, Builder, SystemF (..), Term (..)) where

import Common
import Constant
import Core
import Global
import TextShow (TextShow, fromString, showb)
import Type
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

newtype Builder t a = Builder {builder :: Unique.State (t a)}

build :: Builder t a -> t a
build (Builder s) = Unique.run s

instance SystemF Builder where
  constant k = (Builder . pure) $ ConstantTerm k
  global g = (Builder . pure) $ GlobalTerm g
  letBe value f = Builder $ do
    value' <- builder value
    let t = typeOf value'
    head <- Unique.uniqueId
    let binder = Variable t head
    body <- builder $ f (Builder $ pure $ VariableTerm binder)
    pure (LetTerm value' binder body)
  lambda t f = Builder $ do
    h <- Unique.uniqueId
    let binder = Variable t h
    body <- builder $ f (Builder $ pure $ VariableTerm binder)
    pure (LambdaTerm binder body)
  apply f x = Builder $ do
    f' <- builder f
    x' <- builder x
    pure (ApplyTerm f' x')

data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Variable a -> Term b -> Term b
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

typeOf :: Term a -> Type a
typeOf (VariableTerm (Variable t _)) = t
typeOf (ConstantTerm (IntegerConstant _)) = int
typeOf (GlobalTerm (Global t _)) = t
typeOf (LetTerm _ _ body) = typeOf body
typeOf (LambdaTerm (Variable t _) body) = t -#-> typeOf body
typeOf (ApplyTerm f _) =
  let _ :=> result = typeOf f
   in result

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = showb term <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LambdaTerm binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyTerm f x) = showb x <> fromString "\n" <> showb f

simplify :: SystemF t => Term a -> t Term a
simplify = simp VarMap.empty

simp :: SystemF t => VarMap (X t) -> Term a -> t Term a
simp env (ApplyTerm (LambdaTerm binder@(Variable t _) body) term) =
  let term' = simp env term
   in letBe term' $ \value -> simp (VarMap.insert binder (X value) env) body
simp env (LetTerm term binder@(Variable t _) body) =
  let term' = simp env term
   in letBe term' $ \value -> simp (VarMap.insert binder (X value) env) body
simp env (LambdaTerm binder@(Variable t _) body) =
  let body' = simp env body
   in lambda t $ \value -> simp (VarMap.insert binder (X value) env) body
simp env (ApplyTerm f x) = apply (simp env f) (simp env x)
simp _ (ConstantTerm c) = constant c
simp _ (GlobalTerm g) = global g
simp env (VariableTerm v) = case VarMap.lookup v env of
  Just (X x) -> x

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
inline = inl VarMap.empty

data X t a where
  X :: t Term a -> X t a

inl :: SystemF t => VarMap (X t) -> Term a -> t Term a
inl env (LetTerm term binder@(Variable t _) body) =
  let term' = inl env term
   in if count binder body <= 1 || isSimple term
        then inl (VarMap.insert binder (X term') env) body
        else letBe term' $ \value ->
          inl (VarMap.insert binder (X value) env) body
inl env v@(VariableTerm variable) = case VarMap.lookup variable env of
  Just (X replacement) -> replacement
inl env (ApplyTerm f x) = inl env f `apply` inl env x
inl env (LambdaTerm binder@(Variable t _) body) = lambda t $ \value ->
  inl (VarMap.insert binder (X value) env) body
inl _ (ConstantTerm c) = constant c
inl _ (GlobalTerm g) = global g

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple _ = False
