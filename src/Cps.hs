{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Stack (..), Code (..), Data (..), Builder (..), simplify, inline, typeOf) where

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

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code -> Data (U a)
  LambdaData :: Variable a -> Data (U b) -> Data (U (a :=> b))

data Code where
  GlobalCode :: Global a -> Stack a -> Code
  LetLabelCode :: Stack a -> Label a -> Code -> Code
  LetBeCode :: Data a -> Variable a -> Code -> Code
  ApplyCode :: Data (U (a :=> b)) -> Data a -> Stack b -> Code
  ForceCode :: Data (U a) -> Stack a -> Code
  PopCode :: Stack (a :=> b) -> Label b -> Stack (F a) -> Code
  ThrowCode :: Stack (F a) -> Data a -> Code

data Stack a where
  LabelStack :: Label a -> Stack a
  ToStack :: Variable a -> Code -> Stack (F a)
  PushStack :: Data a -> Stack b -> Stack (a :=> b)

class Cps t where
  constant :: Constant a -> t (Data a)
  global :: Global a -> t (Stack a) -> t Code

  throw :: t (Stack (F a)) -> t (Data a) -> t Code
  force :: t (Data (U a)) -> t (Stack a) -> t Code

  thunk :: Action a -> (t (Stack a) -> t Code) -> t (Data (U a))
  letTo :: Type a -> (t (Data a) -> t Code) -> t (Stack (F a))

  label :: t (Stack a) -> (t (Stack a) -> t Code) -> t Code
  letBe :: t (Data a) -> (t (Data a) -> t Code) -> t Code

  apply :: t (Data (U (a :=> b))) -> t (Data a) -> t (Stack b) -> t Code
  pop :: t (Stack (a :=> b)) -> (t (Stack b) -> t (Stack (F a))) -> t Code

  lambda :: Type a -> (t (Data a) -> t (Data (U b))) -> t (Data (U (a :=> b)))
  push :: t (Data a) -> t (Stack b) -> t (Stack (a :=> b))

  nilStack :: t (Stack R)

  pair :: t (Data a) -> t (Data b) -> t (Data (a :*: b))

  first :: t (Data (a :*: b)) -> t (Data a)
  second :: t (Data (a :*: b)) -> t (Data b)

instance Cps Builder where
  global g k =
    Builder $
      pure (GlobalCode g) <*> builder k
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
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LetBeCode x' v body
  pop x f = Builder $ do
    x' <- builder x
    let (a :=> b) = typeOfStack x'
    t <- pure (Label b) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) (LabelStack t))
    pure $ PopCode x' t body
  apply f x k =
    Builder $
      pure ApplyCode <*> builder f <*> builder x <*> builder k

  constant k = (Builder . pure) $ ConstantData k

  letTo t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ ToStack v body

  thunk t f = Builder $ do
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ LabelStack v))
    pure $ ThunkData v body

  force thnk stk =
    Builder $
      pure ForceCode <*> builder thnk <*> builder stk

  lambda t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ LambdaData v body
  push x k = Builder $ do
    pure PushStack <*> builder x <*> builder k

instance TextShow (Data a) where
  showb (VariableData v) = showb v
  showb (ConstantData k) = showb k
  showb (ThunkData binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " " <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body)))
  showb (LambdaData binder@(Variable t _) body) =
    fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString "\n" <> showb body

instance TextShow (Stack a) where
  showb (ToStack binder@(Variable t _) body) =
    fromString "to " <> showb binder <> fromString ": " <> showb t <> fromString ".\n" <> showb body
  showb (LabelStack v) = showb v
  showb (PushStack x f) = showb x <> fromString " :: " <> showb f

instance TextShow Code where
  showb (GlobalCode g k) = showb g <> fromString " " <> showb k
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

typeOf :: Data a -> Type a
typeOf (ConstantData k) = Constant.typeOf k
typeOf (ThunkData (Label t _) _) = U t
typeOf (VariableData (Variable t _)) = t

typeOfStack :: Stack a -> Action a
typeOfStack (LabelStack (Label t _)) = t
typeOfStack (ToStack (Variable t _) _) = F t
typeOfStack (PushStack h t) =
  let a = typeOf h
      b = typeOfStack t
   in (a :=> b)

simplify :: Data a -> Data a
simplify (ThunkData binder body) = ThunkData binder (simpCode body)
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

inline :: Cps t => Data a -> t (Data a)
inline = inlValue LabelMap.empty VarMap.empty

newtype X t a = X (t (Data a))

newtype L t a = L (t (Stack a))

inlValue :: Cps t => LabelMap (L t) -> VarMap (X t) -> Data a -> t (Data a)
inlValue _ env (VariableData v) =
  let Just (X x) = VarMap.lookup v env
   in x
inlValue lenv env (ThunkData binder@(Label t _) body) = thunk t $ \k ->
  inlCode (LabelMap.insert binder (L k) lenv) env body
inlValue lenv env (LambdaData binder@(Variable t _) body) = lambda t $ \k ->
  inlValue lenv (VarMap.insert binder (X k) env) body
inlValue _ _ (ConstantData k) = Cps.constant k

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
inlCode lenv env (GlobalCode g k) = global g (inlStack lenv env k)

isSimple :: Data a -> Bool
isSimple (ConstantData _) = True
isSimple (VariableData _) = True
isSimple _ = False

isSimpleStack :: Stack a -> Bool
isSimpleStack (LabelStack _) = True
isSimpleStack _ = False

count :: Variable a -> Code -> Int
count v = code
  where
    value :: Data b -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (ThunkData _ body) = code body
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
    code (GlobalCode _ k) = stack k
    code _ = 0

countLabel :: Label a -> Code -> Int
countLabel v = code
  where
    value :: Data b -> Int
    value (ThunkData _ body) = code body
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
    code (GlobalCode _ k) = stack k
    code _ = 0
