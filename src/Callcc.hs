{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (build, Builder (..), Callcc (..), Stack (..), Code (..), Data (..), typeOf, inline, simplify) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Data.Text as T
import Global
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Type
import Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

newtype Builder t a = Builder {builder :: Unique.State (t a)}

build :: Builder t a -> t a
build (Builder s) = Unique.run s

typeOf :: Code a -> Action a
typeOf (LambdaCode (Variable t _) body) = t :=> typeOf body
typeOf (ReturnCode value) = F (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LetToCode _ _ body) = typeOf body
typeOf (CatchCode (Label t _) _) = t
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result
typeOf (ThrowCode _ _) = R

typeOfData :: Data a -> Type a
typeOfData (GlobalData (Global t _)) = t
typeOfData (VariableData (Variable t _)) = t
typeOfData (ConstantData k) = Constant.typeOf k
typeOfData (ThunkData (Label t _) _) = U t

class Callcc t where
  constant :: Constant a -> t Data a
  global :: Global a -> t Data a
  returns :: t Data a -> t Code (F a)
  letTo :: t Code (F a) -> (t Data a -> t Code b) -> t Code b
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b

  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a :=> b)
  apply :: t Code (a :=> b) -> t Data a -> t Code b

  catch :: Action a -> (t Stack a -> t Code R) -> t Code a
  throw :: t Stack a -> t Code a -> t Code R

  thunk :: Action a -> (t Stack a -> t Code R) -> t Data (U a)
  force :: t Data (U a) -> t Stack a -> t Code R

instance Callcc Builder where
  global g = (Builder . pure) $ GlobalData g
  returns value =
    Builder $
      pure ReturnCode <*> builder value
  letTo x f = Builder $ do
    x' <- builder x
    let F t = typeOf x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LetToCode x' v body
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOfData x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LetBeCode x' v body
  lambda t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LambdaCode v body
  apply f x = Builder $ do
    pure ApplyCode <*> builder f <*> builder x
  constant k = (Builder . pure) $ ConstantData k

  thunk t f = Builder $ do
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ LabelData v)
    pure $ ThunkData v body
  force thunk stack =
    Builder $
      pure ForceCode <*> builder thunk <*> builder stack

  catch t f = Builder $ do
    v <- pure (Label t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ LabelData v)
    pure $ CatchCode v body
  throw x f =
    Builder $
      pure ThrowCode <*> builder x <*> builder f

data Code a where
  LambdaCode :: Variable a -> Code b -> Code (a :=> b)
  ApplyCode :: Code (a :=> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  CatchCode :: Label a -> Code R -> Code a
  ThrowCode :: Stack a -> Code a -> Code R
  ForceCode :: Data (U a) -> Stack a -> Code R

data Stack a where
  LabelData :: Label a -> Stack a

data Data a where
  GlobalData :: Global a -> Data a
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code R -> Data (U a)

instance TextShow (Code a) where
  showb (LambdaCode binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchCode binder@(Label t _) body) =
    fromString "catch " <> showb binder <> fromString ": " <> showb t <> fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body))) <> fromString "\n}"
  showb (ThrowCode label body) = showb body <> fromString "\nthrow " <> showb label
  showb (ForceCode thunk stack) = fromString "! " <> showb thunk <> fromString " " <> showb stack

instance TextShow (Data a) where
  showb (ThunkData binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body))) <> fromString "\n}"
  showb (GlobalData g) = showb g
  showb (ConstantData k) = showb k
  showb (VariableData b) = showb b

instance TextShow (Stack a) where
  showb (LabelData b) = showb b

simplify :: Code a -> Code a
simplify = simpCode

simpCode :: Code a -> Code a
simpCode (LetToCode (ReturnCode value) binder body) = simpCode (LetBeCode value binder body)
simpCode (ApplyCode (LambdaCode binder body) value) = simpCode (LetBeCode value binder body)
simpCode (LambdaCode binder body) = LambdaCode binder (simpCode body)
simpCode (ApplyCode f x) = ApplyCode (simpCode f) (simpData x)
simpCode (LetBeCode thing binder body) = LetBeCode (simpData thing) binder (simpCode body)
simpCode (LetToCode act binder body) = LetToCode (simpCode act) binder (simpCode body)
simpCode (CatchCode binder body) = CatchCode binder (simpCode body)
simpCode (ThrowCode stack act) = ThrowCode stack (simpCode act)
simpCode (ForceCode th stk) = ForceCode (simpData th) stk
simpCode (ReturnCode x) = ReturnCode (simpData x)

simpData :: Data a -> Data a
simpData (ThunkData label body) = ThunkData label (simpCode body)
simpData g@(ConstantData _) = g
simpData g@(VariableData _) = g
simpData g@(GlobalData _) = g

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LetToCode action binder body) = code action + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ThrowCode _ f) = code f
    code (ForceCode x _) = value x
    code (CatchCode _ body) = code body
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0

inline :: Callcc t => Code a -> t Code a
inline = inlCode LabelMap.empty VarMap.empty

newtype L t a = L (t Stack a)

inlCode :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Code a -> t Code a
inlCode lenv env (LetBeCode term binder body) =
  let term' = inlValue lenv env term
   in if Callcc.count binder body <= 1
        then inlCode lenv (VarMap.insert binder term' env) body
        else letBe term' $ \x ->
          inlCode lenv (VarMap.insert binder x env) body
inlCode lenv env (LetToCode term binder body) = letTo (inlCode lenv env term) $ \x ->
  inlCode lenv (VarMap.insert binder x env) body
inlCode lenv env (ApplyCode f x) = apply (inlCode lenv env f) (inlValue lenv env x)
inlCode lenv env (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
  inlCode lenv (VarMap.insert binder x env) body
inlCode lenv env (ReturnCode val) = returns (inlValue lenv env val)
inlCode lenv env (ThrowCode x f) = throw (inlStack lenv env x) (inlCode lenv env f)
inlCode lenv env (CatchCode binder@(Label t _) body) = catch t $ \x ->
  inlCode (LabelMap.insert binder (L x) lenv) env body
inlCode lenv env (ForceCode x f) = force (inlValue lenv env x) (inlStack lenv env f)

inlValue :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Data x -> t Data x
inlValue _ _ (GlobalData g) = global g
inlValue _ env (VariableData variable) =
  let Just replacement = VarMap.lookup variable env
   in replacement
inlValue _ _ (ConstantData k) = constant k
inlValue lenv env (ThunkData binder@(Label t _) body) = thunk t $ \x ->
  inlCode (LabelMap.insert binder (L x) lenv) env body

inlStack :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Stack x -> t Stack x
inlStack lenv _ (LabelData l) =
  let Just (L x) = LabelMap.lookup l lenv
   in x
