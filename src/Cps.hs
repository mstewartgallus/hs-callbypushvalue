{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Stack (..), Code (..), Term (..), Builder (..), simplify, inline, typeOf) where

import Common hiding (Stack)
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

data Code where
  LetLabelTerm :: Stack a -> Label a -> Code -> Code
  LetBeTerm :: Term a -> Variable a -> Code -> Code
  ForceTerm :: Term (U a) -> Stack a -> Code
  PopTerm :: Stack (a :=> b) -> Label b -> Stack (F a) -> Code
  ApplyTerm :: Stack (F a) -> Term a -> Code

data Stack a where
  LabelTerm :: Label a -> Stack a
  LetToTerm :: Variable a -> Code -> Stack (F a)
  PushTerm :: Term a -> Stack b -> Stack (a :=> b)

class Cps t where
  constant :: Constant a -> t (Term a)
  global :: Global a -> t (Term a)

  apply :: t (Stack (F a)) -> t (Term a) -> t Code
  force :: t (Term (U a)) -> t (Stack a) -> t Code

  thunk :: Action a -> (t (Stack a) -> t Code) -> t (Term (U a))
  letTo :: Type a -> (t (Term a) -> t Code) -> t (Stack (F a))

  label :: t (Stack a) -> (t (Stack a) -> t Code) -> t Code
  letBe :: t (Term a) -> (t (Term a) -> t Code) -> t Code

  nilStack :: t (Stack R)
  pop :: t (Stack (a :=> b)) -> (t (Stack b) -> t (Stack (F a))) -> t Code
  push :: t (Term a) -> t (Stack b) -> t (Stack (a :=> b))

instance Cps Builder where
  global g = (Builder . pure) $ GlobalTerm g
  apply k x =
    Builder $
      pure ApplyTerm <*> builder k <*> builder x
  label x f = Builder $ do
    x' <- builder x
    let t = typeOfStack x'
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ LabelTerm v)
    pure $ LetLabelTerm x' v body
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOf x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableTerm v)
    pure $ LetBeTerm x' v body
  pop x f = Builder $ do
    x' <- builder x
    let (a :=> b) = typeOfStack x'
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
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm k) = showb k
  showb (ThunkTerm binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " " <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body)))

instance TextShow (Stack a) where
  showb (LetToTerm binder@(Variable t _) body) =
    fromString "to " <> showb binder <> fromString ": " <> showb t <> fromString ".\n" <> showb body
  showb (LabelTerm v) = showb v
  showb (PushTerm x f) = showb x <> fromString " :: " <> showb f

instance TextShow Code where
  showb (LetLabelTerm value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeTerm value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (PopTerm value t body) =
    showb t <> fromString ":\n"
      <> fromString "pop "
      <> showb value
      <> fromString ".\n"
      <> showb body
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

typeOfStack :: Stack a -> Action a
typeOfStack (LabelTerm (Label t _)) = t
typeOfStack (LetToTerm (Variable t _) _) = F t
typeOfStack (PushTerm h t) =
  let a = typeOf h
      b = typeOfStack t
   in (a :=> b)

simplify :: Term a -> Term a
simplify (ThunkTerm binder body) = ThunkTerm binder (simpCode body)
simplify x = x

simpStack :: Stack a -> Stack a
simpStack (LetToTerm binder body) = LetToTerm binder (simpCode body)
simpStack (PushTerm h t) = PushTerm (simplify h) (simpStack t)
simpStack x = x

simpCode :: Code -> Code
simpCode (ForceTerm f x) = ForceTerm (simplify f) (simpStack x)
simpCode (PopTerm value t body) = PopTerm (simpStack value) t (simpStack body)
simpCode (LetLabelTerm thing binder body) = LetLabelTerm (simpStack thing) binder (simpCode body)
simpCode (LetBeTerm thing binder body) = LetBeTerm (simplify thing) binder (simpCode body)
simpCode (ApplyTerm k x) = ApplyTerm (simpStack k) (simplify x)
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
inlValue _ _ (ConstantTerm k) = Cps.constant k
inlValue _ _ (GlobalTerm g) = global g

inlStack :: Cps t => LabelMap (L t) -> VarMap (X t) -> Stack a -> t (Stack a)
inlStack lenv _ (LabelTerm v) =
  let Just (L x) = LabelMap.lookup v lenv
   in x
inlStack lenv env (PushTerm h t) = Cps.push (inlValue lenv env h) (inlStack lenv env t)
inlStack lenv env (LetToTerm binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in inlCode lenv env' body

inlCode :: Cps t => LabelMap (L t) -> VarMap (X t) -> Code -> t Code
inlCode lenv env (LetLabelTerm term binder body) = result
  where
    term' = inlStack lenv env term
    result
      | countLabel binder body <= 1 || isSimpleStack term =
        inlCode (LabelMap.insert binder (L term') lenv) env body
      | otherwise = label term' $ \x ->
        inlCode (LabelMap.insert binder (L x) lenv) env body
inlCode lenv env (LetBeTerm term binder body) = result
  where
    term' = inlValue lenv env term
    result
      | count binder body <= 1 || isSimple term =
        inlCode lenv (VarMap.insert binder (X term') env) body
      | otherwise = letBe term' $ \x ->
        inlCode lenv (VarMap.insert binder (X x) env) body
inlCode lenv env (PopTerm value t body) = pop (inlStack lenv env value) $ \y ->
  inlStack (LabelMap.insert t (L y) lenv) env body
inlCode lenv env (ApplyTerm k x) = apply (inlStack lenv env k) (inlValue lenv env x)
inlCode lenv env (ForceTerm k x) = force (inlValue lenv env k) (inlStack lenv env x)

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple (VariableTerm _) = True
isSimple (GlobalTerm _) = True
isSimple _ = False

isSimpleStack :: Stack a -> Bool
isSimpleStack (LabelTerm _) = True
isSimpleStack _ = False

count :: Variable a -> Code -> Int
count v = code
  where
    value :: Term b -> Int
    value (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (ThunkTerm _ body) = code body
    value _ = 0
    stack :: Stack b -> Int
    stack (PushTerm h t) = value h + stack t
    stack (LetToTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    stack _ = 0
    code :: Code -> Int
    code (LetLabelTerm x binder body) = stack x + code body
    code (LetBeTerm x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (PopTerm x _ body) = stack x + stack body
    code (ApplyTerm k x) = stack k + value x
    code (ForceTerm t k) = value t + stack k
    code _ = 0

countLabel :: Label a -> Code -> Int
countLabel v = code
  where
    value :: Term b -> Int
    value (ThunkTerm _ body) = code body
    value _ = 0
    stack :: Stack b -> Int
    stack (LabelTerm binder) = if AnyLabel v == AnyLabel binder then 1 else 0
    stack (PushTerm h t) = value h + stack t
    stack (LetToTerm binder body) = code body
    stack _ = 0
    code :: Code -> Int
    code (LetLabelTerm x binder body) = stack x + if AnyLabel binder == AnyLabel v then 0 else code body
    code (LetBeTerm x binder body) = value x + code body
    code (PopTerm x _ body) = stack x + stack body
    code (ApplyTerm k x) = stack k + value x
    code (ForceTerm t k) = value t + stack k
    code _ = 0
