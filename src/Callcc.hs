{-# LANGUAGE GADTs, TypeOperators #-}
module Callcc (CodeBuilder (..), DataBuilder (..), build, Code (..), Data (..), typeOf, simplify) where
import Common
import Core
import TextShow
import Unique

data CodeBuilder a where
  GlobalBuilder :: Global a -> CodeBuilder a
  ReturnBuilder :: DataBuilder a -> CodeBuilder (F a)
  LetToBuilder :: CodeBuilder (F a) -> Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder b
  LetBeBuilder :: DataBuilder a -> Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder b
  LambdaBuilder :: Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder (a -> b)
  ApplyBuilder :: CodeBuilder (a -> b) -> DataBuilder a -> CodeBuilder b
  CatchBuilder :: Type a -> (DataBuilder (Stack a) -> CodeBuilder a) -> CodeBuilder a
  ThrowBuilder :: DataBuilder (Stack a) -> CodeBuilder a -> CodeBuilder b

data DataBuilder a where
  VariableBuilder :: Variable a -> DataBuilder a
  ConstantBuilder :: Constant a -> DataBuilder a

buildData :: DataBuilder a -> Data a
buildData (VariableBuilder v) = VariableData v
buildData (ConstantBuilder v) = ConstantData v

build :: CodeBuilder a -> Unique.Stream -> Code a
build (GlobalBuilder v) _ = GlobalCode v
build (ReturnBuilder v) _ = ReturnCode (buildData v)
build (ApplyBuilder f x) stream = ApplyCode (build f stream) (buildData x)
build (LetToBuilder term t body) (Unique.Pick head (Unique.Split left right)) = let
  x = Variable t (toText (showb head))
  term' = build term left
  body' = build (body (VariableBuilder x)) right
  in LetToCode term' x body'
build (LetBeBuilder term t body) (Unique.Pick head tail) = let
  x = Variable t (toText (showb head))
  term' = buildData term
  body' = build (body (VariableBuilder x)) tail
  in LetBeCode term' x body'
build (LambdaBuilder t body) (Unique.Pick head tail) = let
  x = Variable t (toText (showb head))
  body' = build (body (VariableBuilder x)) tail
  in LambdaCode x body'
build (CatchBuilder t body) (Unique.Pick head tail) = let
  -- fixme...
  x = Variable undefined (toText (showb head))
  body' = build (body (VariableBuilder x)) tail
  in CatchCode x body'
build (ThrowBuilder stack value) stream = let
  stack' = buildData stack
  value' = build value stream
  in ThrowCode stack' value'

typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t
typeOf (LambdaCode (Variable t _) body) = t -=> typeOf body
typeOf (ReturnCode value) = ApplyType returns (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LetToCode _ _ body) = typeOf body
typeOf (CatchCode _ body) = typeOf body
typeOf (ApplyCode f _) = let
  _ :=> result = typeOf f
  in result

typeOfData :: Data a -> Type a
typeOfData (ConstantData (IntegerConstant _)) = undefined

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  CatchCode :: Variable (Stack a) -> Code a -> Code a
  ThrowCode :: Data (Stack a) -> Code a -> Code b

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a

data AnyCode where
  AnyCode :: Code a -> AnyCode

data AnyData where
  AnyData :: Data a -> AnyData

instance Eq AnyCode where
  AnyCode (GlobalCode g) == AnyCode (GlobalCode g') = AnyGlobal g == AnyGlobal g'
  AnyCode (LambdaCode binder body) == AnyCode (LambdaCode binder' body') = AnyVariable binder == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetBeCode value binder body) == AnyCode (LetBeCode value' binder' body') = AnyData value == AnyData value' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetToCode act binder body) == AnyCode (LetToCode act' binder' body') = AnyCode act == AnyCode act' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (ApplyCode f x) == AnyCode (ApplyCode f' x') = AnyCode f == AnyCode f' && AnyData x == AnyData x'
  AnyCode (ReturnCode x) == AnyCode (ReturnCode x') = AnyData x == AnyData x'
  AnyCode (CatchCode binder body) == AnyCode (CatchCode binder' body') = AnyVariable binder == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (ThrowCode stack body) == AnyCode (ThrowCode stack' body') = AnyData stack == AnyData stack' && AnyCode body == AnyCode body'
  _ == _ = False

instance Eq AnyData where
  AnyData (ConstantData k) == AnyData (ConstantData k') = AnyConstant k == AnyConstant k'
  AnyData (VariableData v) == AnyData (VariableData v') = AnyVariable v == AnyVariable v'
  _ == _ = False

instance Eq (Code a) where
  x == y = AnyCode x == AnyCode y

instance Eq (Data a) where
  x == y = AnyData x == AnyData y

instance TextShow (Code a) where
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchCode binder body) = fromString "catch " <> showb binder <> fromString ".\n" <> showb body
  showb (ThrowCode label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData b) = showb b

simplify :: Code a -> Code a
simplify (LetToCode (ReturnCode value) binder body) = simplify (LetBeCode value binder body)

simplify (LambdaCode binder body) = LambdaCode binder (simplify body)
simplify (ApplyCode f x) = ApplyCode (simplify f) x
simplify (LetBeCode thing binder body) = LetBeCode thing binder (simplify body)
simplify (LetToCode act binder body) = LetToCode (simplify act) binder (simplify body)
simplify (CatchCode binder body) = CatchCode binder (simplify body)
simplify (ThrowCode stack act) = ThrowCode stack (simplify act)
simplify x = x
