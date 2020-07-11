{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Stack (..), Code (..), Data (..), Builder (..), simplify, inline, typeOf, abstract) where

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
  PushData :: Data a -> Stack b -> Data (a :*: b)

data Code where
  GlobalCode :: Global a -> Stack a -> Code
  LetLabelCode :: Stack a -> Label a -> Code -> Code
  LetBeCode :: Data a -> Variable a -> Code -> Code
  ForceCode :: Data (U a) -> Stack a -> Code
  ThrowCode :: Stack (F a) -> Data a -> Code
  LambdaCode :: Stack (a :=> b) -> Variable a -> Label b -> Code -> Code
  PopCode :: Data (a :*: b) -> Variable a -> Label b -> Code -> Code

data Stack a where
  LabelStack :: Label a -> Stack a
  ToStack :: Variable a -> Code -> Stack (F a)
  ApplyStack :: Data a -> Stack b -> Stack (a :=> b)

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
class Cps t where
  constant :: Constant a -> t (Data a)
  global :: Global a -> t (Stack a) -> t Code

  throw :: t (Stack (F a)) -> t (Data a) -> t Code
  force :: t (Data (U a)) -> t (Stack a) -> t Code

  thunk :: Action a -> (t (Stack a) -> t Code) -> t (Data (U a))
  letTo :: Type a -> (t (Data a) -> t Code) -> t (Stack (F a))

  lambda :: t (Stack (a :=> b)) -> Type a -> Action b -> (t (Data a) -> t (Stack b) -> t Code) -> t Code
  pop :: t (Data (a :*: b)) -> Type a -> Action b -> (t (Data a) -> t (Stack b) -> t Code) -> t Code

  apply :: t (Data a) -> t (Stack b) -> t (Stack (a :=> b))
  push :: t (Data a) -> t (Stack b) -> t (Data (a :*: b))

  nilStack :: t (Stack Void)

instance Cps Builder where
  global g k =
    Builder $
      pure (GlobalCode g) <*> builder k
  throw k x =
    Builder $
      pure ThrowCode <*> builder k <*> builder x

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

  lambda k t a f = Builder $ do
    k' <- builder k
    v <- pure (Variable t) <*> Unique.uniqueId
    t <- pure (Label a) <*> Unique.uniqueId
    body <- builder (f (Builder (pure (VariableData v))) (Builder (pure (LabelStack t))))
    pure $ LambdaCode k' v t body
  pop tuple t a f = Builder $ do
    tuple' <- builder tuple
    v <- pure (Variable t) <*> Unique.uniqueId
    t <- pure (Label a) <*> Unique.uniqueId
    body <- builder (f (Builder (pure (VariableData v))) (Builder (pure (LabelStack t))))
    pure $ PopCode tuple' v t body

  apply x k = Builder $ do
    pure ApplyStack <*> builder x <*> builder k
  push x k = Builder $ do
    pure PushData <*> builder x <*> builder k

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (ThunkData binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " " <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body)))
  showb (PushData x f) = showb x <> fromString " , " <> showb f

instance TextShow (Stack a) where
  showb (LabelStack v) = showb v
  showb (ToStack binder@(Variable t _) body) =
    fromString "to " <> showb binder <> fromString ": " <> showb t <> fromString ".\n" <> showb body
  showb (ApplyStack x f) = showb x <> fromString " :: " <> showb f

instance TextShow Code where
  showb (GlobalCode g k) = fromString "call " <> showb g <> fromString " " <> showb k
  showb (LetLabelCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (ThrowCode k x) = fromString "throw " <> showb k <> fromString " " <> showb x
  showb (ForceCode thnk stk) = fromString "! " <> showb thnk <> fromString " " <> showb stk
  showb (LambdaCode k binder@(Variable t _) label@(Label a _) body) =
    showb k <> fromString " λ " <> showb binder <> fromString ": " <> showb t <> fromString " " <> showb label <> fromString ": " <> showb a <> fromString "\n" <> showb body
  showb (PopCode k binder@(Variable t _) label@(Label a _) body) =
    showb k <> fromString " pop " <> showb binder <> fromString ": " <> showb t <> fromString " " <> showb label <> fromString ": " <> showb a <> fromString "\n" <> showb body

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
typeOfStack (ApplyStack h t) =
  let a = typeOf h
      b = typeOfStack t
   in (a :=> b)

simplify :: Data a -> Data a
simplify (ThunkData binder body) = ThunkData binder (simpCode body)
simplify (PushData h t) = PushData (simplify h) (simpStack t)
simplify x = x

simpStack :: Stack a -> Stack a
simpStack (ToStack binder body) = ToStack binder (simpCode body)
simpStack (ApplyStack h t) = ApplyStack (simplify h) (simpStack t)
simpStack x = x

simpCode :: Code -> Code
simpCode (ThrowCode (ToStack binder body) value) = simpCode (LetBeCode value binder body)
simpCode (ForceCode (ThunkData label body) k) = simpCode (LetLabelCode k label body)
simpCode (ThrowCode k x) = ThrowCode (simpStack k) (simplify x)
simpCode (ForceCode f x) = ForceCode (simplify f) (simpStack x)
simpCode (LetLabelCode thing binder body) = LetLabelCode (simpStack thing) binder (simpCode body)
simpCode (LetBeCode thing binder body) = LetBeCode (simplify thing) binder (simpCode body)
simpCode (GlobalCode g k) = GlobalCode g (simpStack k)
simpCode (PopCode k binder label body) = PopCode (simplify k) binder label (simpCode body)
simpCode (LambdaCode k binder label body) = LambdaCode (simpStack k) binder label (simpCode body)
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
inlValue _ _ (ConstantData k) = Cps.constant k

inlStack :: Cps t => LabelMap (L t) -> VarMap (X t) -> Stack a -> t (Stack a)
inlStack lenv _ (LabelStack v) =
  let Just (L x) = LabelMap.lookup v lenv
   in x
inlStack lenv env (ApplyStack h t) = Cps.apply (inlValue lenv env h) (inlStack lenv env t)
inlStack lenv env (ToStack binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in inlCode lenv env' body

inlCode :: Cps t => LabelMap (L t) -> VarMap (X t) -> Code -> t Code
inlCode lenv env (LambdaCode k binder@(Variable t _) label@(Label a _) body) =
  let k' = inlStack lenv env k
   in lambda k' t a $ \h k ->
        inlCode (LabelMap.insert label (L k) lenv) (VarMap.insert binder (X h) env) body
inlCode lenv env (PopCode k binder@(Variable t _) label@(Label a _) body) =
  let k' = inlValue lenv env k
   in pop k' t a $ \h k ->
        inlCode (LabelMap.insert label (L k) lenv) (VarMap.insert binder (X h) env) body
inlCode lenv env (LetLabelCode term binder@(Label t _) body) = result
  where
    term' = inlStack lenv env term
    result
      | countLabel binder body <= 1 || isSimpleStack term =
        inlCode (LabelMap.insert binder (L term') lenv) env body
      | otherwise =
        force
          ( thunk t $ \x ->
              inlCode (LabelMap.insert binder (L x) lenv) env body
          )
          term'
inlCode lenv env (LetBeCode term binder@(Variable t _) body) = result
  where
    term' = inlValue lenv env term
    result
      | count binder body <= 1 || isSimple term =
        inlCode lenv (VarMap.insert binder (X term') env) body
      | otherwise =
        throw
          ( letTo t $ \x ->
              inlCode lenv (VarMap.insert binder (X x) env) body
          )
          term'
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
    value (PushData h t) = value h + stack t
    value _ = 0
    stack :: Stack b -> Int
    stack (ApplyStack h t) = value h + stack t
    stack (ToStack binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    stack _ = 0
    code :: Code -> Int
    code (LetLabelCode x binder body) = stack x + code body
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (ThrowCode k x) = stack k + value x
    code (ForceCode t k) = value t + stack k
    code (GlobalCode _ k) = stack k
    code (LambdaCode k _ _ body) = stack k + code body
    code (PopCode k _ _ body) = value k + code body

countLabel :: Label a -> Code -> Int
countLabel v = code
  where
    value :: Data b -> Int
    value (ThunkData _ body) = code body
    value (PushData h t) = value h + stack t
    value _ = 0
    stack :: Stack b -> Int
    stack (LabelStack binder) = if AnyLabel v == AnyLabel binder then 1 else 0
    stack (ToStack binder body) = code body
    stack (ApplyStack h t) = value h + stack t
    code :: Code -> Int
    code (LetLabelCode x binder body) = stack x + if AnyLabel binder == AnyLabel v then 0 else code body
    code (LetBeCode x binder body) = value x + code body
    code (ThrowCode k x) = stack k + value x
    code (ForceCode t k) = value t + stack k
    code (GlobalCode _ k) = stack k
    code (LambdaCode k _ _ body) = stack k + code body
    code (PopCode k _ _ body) = value k + code body

abstract :: Cps t => Data a -> t (Data a)
abstract x = abstData x LabelMap.empty VarMap.empty

abstData :: Cps t => Data a -> LabelMap (L t) -> VarMap (X t) -> t (Data a)
abstData (ConstantData k) = \_ _ -> constant k
abstData (VariableData v) = \_ env -> case VarMap.lookup v env of
  Just (X x) -> x
  Nothing -> error "variable not found in environment"
abstData (ThunkData label@(Label t _) body) =
  let body' = abstCode body
   in \lenv env ->
        thunk t $ \k ->
          body' (LabelMap.insert label (L k) lenv) env

abstStack :: Cps t => Stack a -> LabelMap (L t) -> VarMap (X t) -> t (Stack a)
abstStack (LabelStack v) = \lenv _ -> case LabelMap.lookup v lenv of
  Just (L x) -> x
  Nothing -> error "label not found in environment"
abstStack (ToStack binder@(Variable t _) body) =
  let body' = abstCode body
   in \lenv env ->
        letTo t $ \value ->
          body' lenv (VarMap.insert binder (X value) env)
abstStack (ApplyStack h t) =
  let h' = abstData h
      t' = abstStack t
   in \lenv env -> apply (h' lenv env) (t' lenv env)

abstCode :: Cps t => Code -> LabelMap (L t) -> VarMap (X t) -> t Code
abstCode (GlobalCode g k) =
  let k' = abstStack k
   in \lenv env -> global g (k' lenv env)
abstCode (ThrowCode k x) =
  let value' = abstData x
      k' = abstStack k
   in \lenv env -> throw (k' lenv env) (value' lenv env)
abstCode (ForceCode k x) =
  let value' = abstStack x
      k' = abstData k
   in \lenv env -> force (k' lenv env) (value' lenv env)
abstCode (LetBeCode value binder body) =
  let value' = abstData value
      body' = abstCode body
   in \lenv env -> body' lenv (VarMap.insert binder (X (value' lenv env)) env)
abstCode (LetLabelCode value binder body) =
  let value' = abstStack value
      body' = abstCode body
   in \lenv env -> body' (LabelMap.insert binder (L (value' lenv env)) lenv) env
abstCode (LambdaCode k binder@(Variable t _) label@(Label a _) body) =
  let body' = abstCode body
      k' = abstStack k
   in \lenv env ->
        lambda
          (k' lenv env)
          t
          a
          ( \h n ->
              body' (LabelMap.insert label (L n) lenv) (VarMap.insert binder (X h) env)
          )
