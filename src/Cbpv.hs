{-# LANGUAGE GADTs, TypeOperators #-}
module Cbpv (build, CodeBuilder (..), DataBuilder (..), Code (..), Data (..), simplify, intrinsify, inline) where
import Common
import TextShow
import Data.Typeable
import qualified Data.Text as T
import Compiler
import Core
import Unique
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap
import VarMap (VarMap)
import qualified VarMap as VarMap

data CodeBuilder a where
  GlobalBuilder :: Global a -> CodeBuilder a
  ForceBuilder :: DataBuilder (U a) -> CodeBuilder a
  ReturnBuilder :: DataBuilder a -> CodeBuilder (F a)
  LetToBuilder :: CodeBuilder (F a) -> Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder b
  LetBeBuilder :: DataBuilder a -> Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder b
  LambdaBuilder :: Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder (a -> b)
  ApplyBuilder :: CodeBuilder (a -> b) -> DataBuilder a -> CodeBuilder b

data DataBuilder a where
  VariableBuilder :: Variable a -> DataBuilder a
  ConstantBuilder :: Constant a -> DataBuilder a
  ThunkBuilder :: CodeBuilder a -> DataBuilder (U a)

buildData :: DataBuilder a -> Unique.Stream -> Data a
buildData (VariableBuilder v) _ = VariableData v
buildData (ConstantBuilder v) _ = ConstantData v
buildData (ThunkBuilder code) stream = ThunkData (build code stream)

build :: CodeBuilder a -> Unique.Stream -> Code a
build (GlobalBuilder v) _ = GlobalCode v
build (ApplyBuilder f x) (Unique.Split left right) = ApplyCode (build f left) (buildData x right)
build (LetToBuilder term t body) (Unique.Pick head (Unique.Split left right)) = let
  x = Variable t (toText (showb head))
  term' = build term left
  body' = build (body (VariableBuilder x)) right
  in LetToCode term' x body'
build (LetBeBuilder term t body) (Unique.Pick head (Unique.Split left right)) = let
  x = Variable t (toText (showb head))
  term' = buildData term left
  body' = build (body (VariableBuilder x)) right
  in LetBeCode term' x body'
build (LambdaBuilder t body) (Unique.Pick head tail) = let
  x = Variable t (toText (showb head))
  body' = build (body (VariableBuilder x)) tail
  in LambdaCode x body'

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ForceCode :: Data (U a) -> Code a
  ReturnCode :: Data a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Data a -> Variable a -> Code b -> Code b

data Data a where
  VariableData :: Variable a -> Data a
  ConstantData :: Constant a -> Data a
  ThunkData ::  Code a -> Data (U a)

data AnyCode where
  AnyCode :: Code a -> AnyCode

instance Eq AnyCode where
  AnyCode (GlobalCode g) == AnyCode (GlobalCode g') = AnyGlobal g == AnyGlobal g'
  AnyCode (LambdaCode binder body) == AnyCode (LambdaCode binder' body') = AnyVariable binder == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetBeCode value binder body) == AnyCode (LetBeCode value' binder' body') = AnyData value == AnyData value' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (LetToCode act binder body) == AnyCode (LetToCode act' binder' body') = AnyCode act == AnyCode act' && AnyVariable binder' == AnyVariable binder' && AnyCode body == AnyCode body'
  AnyCode (ApplyCode f x) == AnyCode (ApplyCode f' x') = AnyCode f == AnyCode f' && AnyData x == AnyData x'
  AnyCode (ForceCode x) == AnyCode (ForceCode x') = AnyData x == AnyData x'
  AnyCode (ReturnCode x) == AnyCode (ReturnCode x') = AnyData x == AnyData x'
  _ == _ = False

instance Eq (Code a) where
  x == y = AnyCode x == AnyCode y

data AnyData where
  AnyData :: Data a -> AnyData

instance Eq AnyData where
  AnyData (ConstantData k) == AnyData (ConstantData k') = AnyConstant k == AnyConstant k'
  AnyData (VariableData v) == AnyData (VariableData v') = AnyVariable v == AnyVariable v'
  AnyData (ThunkData code) == AnyData (ThunkData code') = AnyCode code == AnyCode code'
  _ == _ = False

instance Eq (Data a) where
  x == y = AnyData x == AnyData y

instance TextShow (Code a) where
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ForceCode thunk) = fromString "! " <> showb thunk
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body

instance TextShow (Data a) where
  showb (VariableData v) = showb v
  showb (ConstantData k) = showb k
  showb (ThunkData code) = fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb code))) <> fromString "\n}"

{-
Simplify Call By Push Data Inverses

So far we handle:

- force (thunk X) to X
- thunk (force X) to X
-}
simplify :: Code a -> Code a
simplify (ForceCode (ThunkData x)) = simplify x
simplify (ForceCode x) = ForceCode (simplifyData x)
simplify (ApplyCode (LambdaCode binder body) value) = simplify (LetBeCode value binder body)
simplify (LambdaCode binder body) = let
  body' = simplify body
  in LambdaCode binder body'
simplify (ApplyCode f x) = ApplyCode (simplify f) (simplifyData x)
simplify (ReturnCode value) = ReturnCode (simplifyData value)
simplify (LetBeCode value binder body) = LetBeCode (simplifyData value) binder (simplify body)
simplify (LetToCode action binder body) = LetToCode (simplify action) binder (simplify body)
simplify x = x

simplifyData :: Data a -> Data a
simplifyData (ThunkData (ForceCode x)) = simplifyData x
simplifyData (ThunkData x) = ThunkData (simplify x)
simplifyData x = x


count :: Variable a -> Code b -> Int
count v = code where
  code :: Code x -> Int
  code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
  code (LetToCode action binder body) = code action + if AnyVariable binder == AnyVariable v then 0 else code body
  code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
  code (ApplyCode f x) = code f + value x
  code (ForceCode thunk) = value thunk
  code (ReturnCode x) = value x
  code _ = 0

  value :: Data x -> Int
  value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
  value (ThunkData c) = code c
  value _ = 0

inline :: Code a -> Code a
inline = inline' VarMap.empty

inline' :: VarMap Data -> Code a -> Code a
inline' map = code where
  code :: Code x -> Code x
  code (LetBeCode term binder body) = if count binder body <= 1
    then inline' (VarMap.insert binder (value term) map) body
    else LetBeCode (value term) binder (inline' (VarMap.delete binder map) body)
  code (LetToCode term binder body) = LetToCode (code term) binder (inline' (VarMap.delete binder map) body)
  code (ApplyCode f x) = ApplyCode (code f) (value x)
  code (LambdaCode binder body) = LambdaCode binder (inline' (VarMap.delete binder map) body)
  code term = term

  value :: Data x -> Data x
  value v@(VariableData variable) = case VarMap.lookup variable map of
    Nothing -> v
    Just replacement -> replacement
  value (ThunkData c) = ThunkData (code c)
  value x = x



-- Fixme... use a different file for this?

intrinsify :: Code a -> Compiler (Code a)
intrinsify global@(GlobalCode g) = case GlobalMap.lookup g intrinsics of
  Nothing -> pure global
  Just (Intrinsic intrinsic) -> intrinsic
intrinsify (LambdaCode binder x) = pure (LambdaCode binder) <*> intrinsify x
intrinsify (ApplyCode f x) = pure ApplyCode <*> intrinsify f <*> intrinsifyData x
intrinsify (ForceCode x) = pure ForceCode <*> intrinsifyData x
intrinsify (ReturnCode x) = pure ReturnCode <*> intrinsifyData x
intrinsify (LetBeCode value binder body) = pure LetBeCode <*> intrinsifyData value <*> pure binder <*> intrinsify body
intrinsify (LetToCode action binder body) = pure LetToCode <*> intrinsify action <*> pure binder <*> intrinsify body

intrinsifyData :: Data a -> Compiler (Data a)
intrinsifyData (ThunkData code) = pure ThunkData <*> intrinsify code
intrinsifyData x = pure x

newtype Intrinsic a = Intrinsic (Compiler (Code a))

intrinsics :: GlobalMap Intrinsic
intrinsics = GlobalMap.fromList [
     GlobalMap.Entry plus (Intrinsic plusIntrinsic)
  ]

plusIntrinsic :: Compiler (Code (F Integer :-> F Integer :-> F Integer))
plusIntrinsic = do
  x' <- getVariable (ApplyType thunk int)
  y' <- getVariable (ApplyType thunk int)
  x'' <- getVariable intRaw
  y'' <- getVariable intRaw
  pure $
    LambdaCode x' $
    LambdaCode y' $
    LetToCode (ForceCode (VariableData x')) x'' $
    LetToCode (ForceCode (VariableData y')) y'' $
    ApplyCode (ApplyCode (GlobalCode strictPlus) (VariableData x'')) (VariableData y'')
