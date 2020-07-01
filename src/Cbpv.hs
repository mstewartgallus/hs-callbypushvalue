{-# LANGUAGE GADTs, TypeOperators #-}
module Cbpv (Code (..), Value (..), simplify, intrinsify) where
import Common
import TextShow
import Data.Typeable
import qualified Data.Text as T
import Compiler
import Core
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap

data Code a where
  ConstantCode :: Constant a -> Code a
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Value a -> Code b
  ForceCode :: Value (U a) -> Code a
  ReturnCode :: Value a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Value a -> Variable a -> Code b -> Code b

data Value a where
  VariableValue :: Variable a -> Value a
  ThunkValue ::  Code a -> Value (U a)

data AnyCode where
  AnyCode :: Code a -> AnyCode

instance Eq AnyCode where
  AnyCode (ConstantCode k) == AnyCode (ConstantCode k') = AnyConstant k == AnyConstant k'
  AnyCode (GlobalCode g) == AnyCode (GlobalCode g') = AnyGlobal g == AnyGlobal g'
  AnyCode (LambdaCode binder body) == AnyCode (LambdaCode binder' body') = AnyVariable binder == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetBeCode value binder body) == AnyCode (LetBeCode value' binder' body') = AnyValue value == AnyValue value' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetToCode act binder body) == AnyCode (LetToCode act' binder' body') = AnyCode act == AnyCode act' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (ApplyCode f x) == AnyCode (ApplyCode f' x') = AnyCode f == AnyCode f' && AnyValue x == AnyValue x'
  AnyCode (ForceCode x) == AnyCode (ForceCode x') = AnyValue x == AnyValue x'
  AnyCode (ReturnCode x) == AnyCode (ReturnCode x') = AnyValue x == AnyValue x'
  _ == _ = False

instance Eq (Code a) where
  x == y = AnyCode x == AnyCode y

data AnyValue where
  AnyValue :: Value a -> AnyValue

instance Eq AnyValue where
  AnyValue (VariableValue v) == AnyValue (VariableValue v') = AnyVariable v == AnyVariable v'
  AnyValue (ThunkValue code) == AnyValue (ThunkValue code') = AnyCode code == AnyCode code'
  _ == _ = False

instance Eq (Value a) where
  x == y = AnyValue x == AnyValue y

instance TextShow (Code a) where
  showb (ConstantCode k) = showb k
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ForceCode thunk) = fromString "! " <> showb thunk
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body

instance TextShow (Value a) where
  showb (VariableValue v) = showb v
  showb (ThunkValue code) = fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb code))) <> fromString "\n}"

{-
Simplify Call By Push Value Inverses

So far we handle:

- force (thunk X) to X
- thunk (force X) to X
-}
simplify :: Code a -> Code a
simplify (ForceCode (ThunkValue x)) = simplify x
simplify (ForceCode x) = ForceCode (simplifyValue x)
-- FIXME
simplify (LambdaCode binder body) = let
  body' = simplify body
  in LambdaCode binder body'
simplify (ApplyCode (LambdaCode binder body) value) = simplify (LetBeCode value binder body)
simplify (ApplyCode f x) = ApplyCode (simplify f) (simplifyValue x)
simplify (ReturnCode value) = ReturnCode (simplifyValue value)
simplify (LetBeCode value binder body) = LetBeCode (simplifyValue value) binder (simplify body)
simplify (LetToCode action binder body) = LetToCode (simplify action) binder (simplify body)
simplify x = x

simplifyValue :: Value a -> Value a
simplifyValue (ThunkValue (ForceCode x)) = simplifyValue x
simplifyValue (ThunkValue x) = ThunkValue (simplify x)
simplifyValue x = x




intrinsify :: Code a -> Compiler (Code a)
intrinsify global@(GlobalCode g) = case GlobalMap.lookup g intrinsics of
  Nothing -> pure global
  Just (Intrinsic intrinsic) -> intrinsic
intrinsify (LambdaCode binder x) = pure (LambdaCode binder) <*> intrinsify x
intrinsify (ApplyCode f x) = pure ApplyCode <*> intrinsify f <*> intrinsifyValue x
intrinsify (ForceCode x) = pure ForceCode <*> intrinsifyValue x
intrinsify (ReturnCode x) = pure ReturnCode <*> intrinsifyValue x
intrinsify (LetBeCode value binder body) = pure LetBeCode <*> intrinsifyValue value <*> pure binder <*> intrinsify body
intrinsify (LetToCode action binder body) = pure LetToCode <*> intrinsify action <*> pure binder <*> intrinsify body
intrinsify x = pure x

intrinsifyValue :: Value a -> Compiler (Value a)
intrinsifyValue (ThunkValue code) = pure ThunkValue <*> intrinsify code
intrinsifyValue x = pure x

newtype Intrinsic a = Intrinsic (Compiler (Code a))

intrinsics :: GlobalMap Intrinsic
intrinsics = GlobalMap.fromList [
     GlobalMap.Entry plus (Intrinsic plusIntrinsic)
  ]

plusIntrinsic :: Compiler (Code (F Integer :-> F Integer :-> F Integer))
plusIntrinsic = do
  let Type int' = int
  let Type thunk' = thunk
  x' <- getVariable (Type (ApplyName thunk' int'))
  y' <- getVariable (Type (ApplyName thunk' int'))
  x'' <- getVariable intRaw
  y'' <- getVariable intRaw
  pure $
    LambdaCode x' $
    LambdaCode y' $
    LetToCode (ForceCode (VariableValue x')) x'' $
    LetToCode (ForceCode (VariableValue y')) y'' $
    ApplyCode (ApplyCode (GlobalCode strictPlus) (VariableValue x'')) (VariableValue y'')
