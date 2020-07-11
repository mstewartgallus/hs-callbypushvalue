{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Stack (..), Code (..), Term (..), Builder (..), simplify, inline, typeOf) where

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
  ThunkTerm :: Label a -> Code -> Term (U a)
  LambdaTerm :: Variable a -> Term (U b) -> Term (U (a :=> b))

data Code where
  LetLabelCode :: Stack a -> Label a -> Code -> Code
  LetBeCode :: Term a -> Variable a -> Code -> Code
  ForceCode :: Term (U a) -> Stack a -> Code
  PopCode :: Stack (a :=> b) -> Label b -> Stack (F a) -> Code
  ThrowCode :: Stack (F a) -> Term a -> Code

data Stack a where
  LabelStack :: Label a -> Stack a
  ToStack :: Variable a -> Code -> Stack (F a)
  PushStack :: Term a -> Stack b -> Stack (a :=> b)

class Cps t where
  constant :: Constant a -> t (Term a)
  global :: Global a -> t (Term a)

  throw :: t (Stack (F a)) -> t (Term a) -> t Code
  force :: t (Term (U a)) -> t (Stack a) -> t Code

  thunk :: Action a -> (t (Stack a) -> t Code) -> t (Term (U a))
  letTo :: Type a -> (t (Term a) -> t Code) -> t (Stack (F a))

  label :: t (Stack a) -> (t (Stack a) -> t Code) -> t Code
  letBe :: t (Term a) -> (t (Term a) -> t Code) -> t Code

  apply :: t (Term (U (a :=> b))) -> t (Term a) -> t (Stack b) -> t Code
  pop :: t (Stack (a :=> b)) -> (t (Stack b) -> t (Stack (F a))) -> t Code

  lambda :: Type a -> (t (Term a) -> t (Term (U b))) -> t (Term (U (a :=> b)))
  push :: t (Term a) -> t (Stack b) -> t (Stack (a :=> b))

  nilStack :: t (Stack R)

instance Cps Builder where
  global g = (Builder . pure) $ GlobalTerm g
  throw k x =
    Builder $
      pure ThrowCode <*> builder k <*> builder x
  label x f = Builder $ do
    x' <- builder x
    let t = typeOfStack x'
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ LabelStack v)
    pure $ LetLabelCode x' v body
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOf x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableTerm v)
    pure $ LetBeCode x' v body
  pop x f = Builder $ do
    x' <- builder x
    let (a :=> b) = typeOfStack x'
    t <- pure (Label b) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) (LabelStack t))
    pure $ PopCode x' t body
  constant k = (Builder . pure) $ ConstantTerm k

  letTo t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableTerm v))
    pure $ ToStack v body

  thunk t f = Builder $ do
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ LabelStack v))
    pure $ ThunkTerm v body

  force thnk stk =
    Builder $
      pure ForceCode <*> builder thnk <*> builder stk

  lambda t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableTerm v))
    pure $ LambdaTerm v body
  push x k = Builder $ do
    pure PushStack <*> builder x <*> builder k

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm k) = showb k
  showb (ThunkTerm binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " " <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body)))
  showb (LambdaTerm binder@(Variable t _) body) =
    fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString "\n" <> showb body

instance TextShow (Stack a) where
  showb (ToStack binder@(Variable t _) body) =
    fromString "to " <> showb binder <> fromString ": " <> showb t <> fromString ".\n" <> showb body
  showb (LabelStack v) = showb v
  showb (PushStack x f) = showb x <> fromString " :: " <> showb f

instance TextShow Code where
  showb (LetLabelCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (PopCode value t body) =
    showb t <> fromString ":\n"
      <> fromString "pop "
      <> showb value
      <> fromString ".\n"
      <> showb body
  showb (ThrowCode k x) = fromString "jump " <> showb k <> fromString " " <> showb x
  showb (ForceCode thnk stk) = fromString "! " <> showb thnk <> fromString " " <> showb stk

build :: Builder a -> a
build (Builder s) = Unique.run s

newtype Builder a = Builder {builder :: Unique.State a}

typeOf :: Term a -> Type a
typeOf (GlobalTerm (Global t _)) = t
typeOf (ConstantTerm k) = Constant.typeOf k
typeOf (ThunkTerm (Label t _) _) = U t
typeOf (VariableTerm (Variable t _)) = t

typeOfStack :: Stack a -> Action a
typeOfStack (LabelStack (Label t _)) = t
typeOfStack (ToStack (Variable t _) _) = F t
typeOfStack (PushStack h t) =
  let a = typeOf h
      b = typeOfStack t
   in (a :=> b)

simplify :: Term a -> Term a
simplify (ThunkTerm binder body) = ThunkTerm binder (simpCode body)
simplify x = x

simpStack :: Stack a -> Stack a
simpStack (ToStack binder body) = ToStack binder (simpCode body)
simpStack (PushStack h t) = PushStack (simplify h) (simpStack t)
simpStack x = x

simpCode :: Code -> Code
simpCode (ForceCode f x) = ForceCode (simplify f) (simpStack x)
simpCode (PopCode value t body) = PopCode (simpStack value) t (simpStack body)
simpCode (LetLabelCode thing binder body) = LetLabelCode (simpStack thing) binder (simpCode body)
simpCode (LetBeCode thing binder body) = LetBeCode (simplify thing) binder (simpCode body)
simpCode (ThrowCode k x) = ThrowCode (simpStack k) (simplify x)
simpCode x = x

inline :: Cps t => Term a -> t (Term a)
inline = inlValue LabelMap.empty VarMap.empty

newtype X t a = X (t (Term a))

newtype L t a = L (t (Stack a))

inlValue :: Cps t => LabelMap (L t) -> VarMap (X t) -> Term a -> t (Term a)
inlValue _ env (VariableTerm v) =
  let Just (X x) = VarMap.lookup v env
   in x
inlValue lenv env (ThunkTerm binder@(Label t _) body) = thunk t $ \k ->
  inlCode (LabelMap.insert binder (L k) lenv) env body
inlValue lenv env (LambdaTerm binder@(Variable t _) body) = lambda t $ \k ->
  inlValue lenv (VarMap.insert binder (X k) env) body
inlValue _ _ (ConstantTerm k) = Cps.constant k
inlValue _ _ (GlobalTerm g) = global g

inlStack :: Cps t => LabelMap (L t) -> VarMap (X t) -> Stack a -> t (Stack a)
inlStack lenv _ (LabelStack v) =
  let Just (L x) = LabelMap.lookup v lenv
   in x
inlStack lenv env (PushStack h t) = Cps.push (inlValue lenv env h) (inlStack lenv env t)
inlStack lenv env (ToStack binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in inlCode lenv env' body

inlCode :: Cps t => LabelMap (L t) -> VarMap (X t) -> Code -> t Code
inlCode lenv env (LetLabelCode term binder body) = result
  where
    term' = inlStack lenv env term
    result
      | countLabel binder body <= 1 || isSimpleStack term =
        inlCode (LabelMap.insert binder (L term') lenv) env body
      | otherwise = label term' $ \x ->
        inlCode (LabelMap.insert binder (L x) lenv) env body
inlCode lenv env (LetBeCode term binder body) = result
  where
    term' = inlValue lenv env term
    result
      | count binder body <= 1 || isSimple term =
        inlCode lenv (VarMap.insert binder (X term') env) body
      | otherwise = letBe term' $ \x ->
        inlCode lenv (VarMap.insert binder (X x) env) body
inlCode lenv env (PopCode value t body) = pop (inlStack lenv env value) $ \y ->
  inlStack (LabelMap.insert t (L y) lenv) env body
inlCode lenv env (ThrowCode k x) = throw (inlStack lenv env k) (inlValue lenv env x)
inlCode lenv env (ForceCode k x) = force (inlValue lenv env k) (inlStack lenv env x)

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple (VariableTerm _) = True
isSimple (GlobalTerm _) = True
isSimple _ = False

isSimpleStack :: Stack a -> Bool
isSimpleStack (LabelStack _) = True
isSimpleStack _ = False

count :: Variable a -> Code -> Int
count v = code
  where
    value :: Term b -> Int
    value (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (ThunkTerm _ body) = code body
    value _ = 0
    stack :: Stack b -> Int
    stack (PushStack h t) = value h + stack t
    stack (ToStack binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    stack _ = 0
    code :: Code -> Int
    code (LetLabelCode x binder body) = stack x + code body
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (PopCode x _ body) = stack x + stack body
    code (ThrowCode k x) = stack k + value x
    code (ForceCode t k) = value t + stack k
    code _ = 0

countLabel :: Label a -> Code -> Int
countLabel v = code
  where
    value :: Term b -> Int
    value (ThunkTerm _ body) = code body
    value _ = 0
    stack :: Stack b -> Int
    stack (LabelStack binder) = if AnyLabel v == AnyLabel binder then 1 else 0
    stack (PushStack h t) = value h + stack t
    stack (ToStack binder body) = code body
    stack _ = 0
    code :: Code -> Int
    code (LetLabelCode x binder body) = stack x + if AnyLabel binder == AnyLabel v then 0 else code body
    code (LetBeCode x binder body) = value x + code body
    code (PopCode x _ body) = stack x + stack body
    code (ThrowCode k x) = stack k + value x
    code (ForceCode t k) = value t + stack k
    code _ = 0
