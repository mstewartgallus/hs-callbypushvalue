{-# LANGUAGE GADTs, TypeOperators #-}
module Callcc (Code (..), Value (..), simplify) where
import Common
import TextShow

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Value a -> Code b
  ReturnCode :: Value a -> Code (F a)
  LetBeCode :: Value a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  CatchCode :: Variable (Stack a) -> Code a -> Code a
  ThrowCode :: Value (Stack a) -> Code a -> Code b

data Value a where
  ConstantValue :: Constant a -> Value a
  VariableValue :: Variable a -> Value a

data AnyCode where
  AnyCode :: Code a -> AnyCode

data AnyValue where
  AnyValue :: Value a -> AnyValue

instance Eq AnyCode where
  AnyCode (GlobalCode g) == AnyCode (GlobalCode g') = AnyGlobal g == AnyGlobal g'
  AnyCode (LambdaCode binder body) == AnyCode (LambdaCode binder' body') = AnyVariable binder == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetBeCode value binder body) == AnyCode (LetBeCode value' binder' body') = AnyValue value == AnyValue value' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetToCode act binder body) == AnyCode (LetToCode act' binder' body') = AnyCode act == AnyCode act' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (ApplyCode f x) == AnyCode (ApplyCode f' x') = AnyCode f == AnyCode f' && AnyValue x == AnyValue x'
  AnyCode (ReturnCode x) == AnyCode (ReturnCode x') = AnyValue x == AnyValue x'
  AnyCode (CatchCode binder body) == AnyCode (CatchCode binder' body') = AnyVariable binder == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (ThrowCode stack body) == AnyCode (ThrowCode stack' body') = AnyValue stack == AnyValue stack' && AnyCode body == AnyCode body'
  _ == _ = False

instance Eq AnyValue where
  AnyValue (ConstantValue k) == AnyValue (ConstantValue k') = AnyConstant k == AnyConstant k'
  AnyValue (VariableValue v) == AnyValue (VariableValue v') = AnyVariable v == AnyVariable v'
  _ == _ = False

instance Eq (Code a) where
  x == y = AnyCode x == AnyCode y

instance Eq (Value a) where
  x == y = AnyValue x == AnyValue y

instance TextShow (Code a) where
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchCode binder body) = fromString "catch " <> showb binder <> fromString ".\n" <> showb body
  showb (ThrowCode label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body

instance TextShow (Value a) where
  showb (ConstantValue k) = showb k
  showb (VariableValue b) = showb b

simplify :: Code a -> Code a
simplify (LetToCode (ReturnCode value) binder body) = simplify (LetBeCode value binder body)

simplify (LambdaCode binder body) = LambdaCode binder (simplify body)
simplify (ApplyCode f x) = ApplyCode (simplify f) x
simplify (LetBeCode thing binder body) = LetBeCode thing binder (simplify body)
simplify (LetToCode act binder body) = LetToCode (simplify act) binder (simplify body)
simplify (CatchCode binder body) = CatchCode binder (simplify body)
simplify (ThrowCode stack act) = ThrowCode stack (simplify act)
simplify x = x
