{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (build, Builder (..), Callcc (..), Code (..), Data (..), typeOf, inline, simplify) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Data.Text as T
import Global
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
typeOf (CatchCode _ body) = typeOf body
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result
typeOf (ThrowCode t _ _) = t
typeOf _ = undefined

typeOfData :: Data a -> Type a
typeOfData (GlobalData (Global t _)) = t
typeOfData (VariableData (Variable t _)) = t
typeOfData (ConstantData k) = Constant.typeOf k

class Callcc t where
  constant :: Constant a -> t Data a
  global :: Global a -> t Data a
  returns :: t Data a -> t Code (F a)
  letTo :: t Code (F a) -> (t Data a -> t Code b) -> t Code b
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b
  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a :=> b)
  apply :: t Code (a :=> b) -> t Data a -> t Code b
  catch :: Action a -> (t Data (Stack a) -> t Code a) -> t Code a
  throw :: Action b -> t Data (Stack a) -> t Code a -> t Code b

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

  catch t f = Builder $ do
    v <- pure (Variable (StackType t)) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ CatchCode v body
  throw t x f =
    Builder $
      pure (ThrowCode t) <*> builder x <*> builder f

data Code a where
  LambdaCode :: Variable a -> Code b -> Code (a :=> b)
  ApplyCode :: Code (a :=> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  CatchCode :: Variable (Stack a) -> Code a -> Code a
  ThrowCode :: Action b -> Data (Stack a) -> Code a -> Code b

data Data a where
  GlobalData :: Global a -> Data a
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a

instance TextShow (Code a) where
  showb (LambdaCode binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchCode binder@(Variable t _) body) =
    fromString "catch " <> showb binder <> fromString ": " <> showb t <> fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body))) <> fromString "\n}"
  showb (ThrowCode _ label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body

instance TextShow (Data a) where
  showb (GlobalData g) = showb g
  showb (ConstantData k) = showb k
  showb (VariableData b) = showb b

simplify :: Code a -> Code a
simplify (LetToCode (ReturnCode value) binder body) = simplify (LetBeCode value binder body)
simplify (ApplyCode (LambdaCode binder body) value) = simplify (LetBeCode value binder body)
simplify (LambdaCode binder body) = LambdaCode binder (simplify body)
simplify (ApplyCode f x) = ApplyCode (simplify f) x
simplify (LetBeCode thing binder body) = LetBeCode thing binder (simplify body)
simplify (LetToCode act binder body) = LetToCode (simplify act) binder (simplify body)
simplify (CatchCode binder body) = CatchCode binder (simplify body)
simplify (ThrowCode t stack act) = ThrowCode t stack (simplify act)
simplify x = x

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LetToCode action binder body) = code action + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ThrowCode _ x f) = value x + code f
    code (CatchCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0

inline :: Callcc t => Code a -> t Code a
inline = inlCode VarMap.empty

inlCode :: Callcc t => VarMap (t Data) -> Code a -> t Code a
inlCode env (LetBeCode term binder body) =
  let term' = inlValue env term
   in if Callcc.count binder body <= 1
        then inlCode (VarMap.insert binder term' env) body
        else letBe term' $ \x ->
          inlCode (VarMap.insert binder x env) body
inlCode env (LetToCode term binder body) = letTo (inlCode env term) $ \x ->
  inlCode (VarMap.insert binder x env) body
inlCode env (ApplyCode f x) = apply (inlCode env f) (inlValue env x)
inlCode env (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
  inlCode (VarMap.insert binder x env) body
inlCode env (ReturnCode val) = returns (inlValue env val)
inlCode env (ThrowCode t x f) = throw t (inlValue env x) (inlCode env f)
inlCode env (CatchCode binder@(Variable (StackType t) _) body) = catch t $ \x ->
  inlCode (VarMap.insert binder x env) body
inlCode _ _ = undefined

inlValue :: Callcc t => VarMap (t Data) -> Data x -> t Data x
inlValue _ (GlobalData g) = global g
inlValue env (VariableData variable) =
  let Just replacement = VarMap.lookup variable env
   in replacement
inlValue _ (ConstantData k) = constant k
