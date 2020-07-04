{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (CodeBuilder (..), DataBuilder (..), build, Code (..), Data (..), typeOf, inline, simplify, constant, throw, global, returns, letTo, letBe, lambda, apply, catch, throw) where

import Common
import Core
import Data.Text as T
import TextShow
import Unique
import qualified VarMap
import VarMap (VarMap)

newtype CodeBuilder a = CodeBuilder {build :: Unique.Stream -> Code a}

newtype DataBuilder a = DataBuilder {buildData :: Unique.Stream -> Data a}

global :: Global a -> CodeBuilder a
global g = (CodeBuilder . const) $ GlobalCode g

returns :: DataBuilder a -> CodeBuilder (F a)
returns value = CodeBuilder $ \stream ->
  ReturnCode (buildData value stream)

letTo :: CodeBuilder (F a) -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder b
letTo x f = CodeBuilder $ \(Unique.Pick h (Unique.Split l r)) ->
  let x' = build x l
      ReturnsType t = typeOf x'
      v = Variable t h
      body = build (f ((DataBuilder . const) $ VariableData v)) r
   in LetToCode x' v body

letBe :: DataBuilder a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder b
letBe x f = CodeBuilder $ \(Unique.Pick h (Unique.Split l r)) ->
  let x' = buildData x l
      t = typeOfData x'
      v = Variable t h
      body = build (f ((DataBuilder . const) $ VariableData v)) r
   in LetBeCode x' v body

lambda :: Type a -> (DataBuilder a -> CodeBuilder b) -> CodeBuilder (a -> b)
lambda t f = CodeBuilder $ \(Unique.Pick h stream) ->
  let v = Variable t h
      body = build (f ((DataBuilder . const) $ VariableData v)) stream
   in LambdaCode v body

apply :: CodeBuilder (a -> b) -> DataBuilder a -> CodeBuilder b
apply f x = CodeBuilder $ \(Unique.Split l r) ->
  let f' = build f l
      x' = buildData x r
   in ApplyCode f' x'

catch :: Type a -> (DataBuilder (Stack a) -> CodeBuilder Nil) -> CodeBuilder a
catch t f = CodeBuilder $ \(Unique.Pick h stream) ->
  let v = Variable (ApplyType stack t) h
      body = build (f ((DataBuilder . const) $ VariableData v)) stream
   in CatchCode v body

throw :: DataBuilder (Stack a) -> CodeBuilder a -> CodeBuilder Nil
throw x f = CodeBuilder $ \(Unique.Split l r) ->
  let x' = buildData x l
      f' = build f r
   in ThrowCode x' f'

constant :: Constant a -> DataBuilder a
constant k = (DataBuilder . const) $ ConstantData k

typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t
typeOf (LambdaCode (Variable t _) body) = t -=> typeOf body
typeOf (ReturnCode value) = ApplyType returnsType (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LetToCode _ _ body) = typeOf body
typeOf (CatchCode (Variable (StackType x) _) _) = x
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result
typeOf (ThrowCode _ _) = undefined

typeOfData :: Data a -> Type a
typeOfData (VariableData (Variable t _)) = t
typeOfData (ConstantData (IntegerConstant _)) = intRaw

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  CatchCode :: Variable (Stack a) -> Code Nil -> Code a
  ThrowCode :: Data (Stack a) -> Code a -> Code Nil

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a

instance TextShow (Code a) where
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchCode binder body) =
    fromString "catch " <> showb binder <> fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body))) <> fromString "\n}"
  showb (ThrowCode label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body

instance TextShow (Data a) where
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
simplify (ThrowCode stack act) = ThrowCode stack (simplify act)
simplify x = x

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LetToCode action binder body) = code action + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ThrowCode x f) = value x + code f
    code (CatchCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0

inline :: Code a -> CodeBuilder a
inline = inline' VarMap.empty

inline' :: VarMap DataBuilder -> Code a -> CodeBuilder a
inline' map = code
  where
    code :: Code x -> CodeBuilder x
    code (LetBeCode term binder body) =
      if Callcc.count binder body <= 1
        then inline' (VarMap.insert binder (value term) map) body
        else letBe (value term) $ \x ->
          inline' (VarMap.insert binder x map) body
    code (LetToCode term binder body) = letTo (code term) $ \x ->
      inline' (VarMap.insert binder x map) body
    code (ApplyCode f x) = apply (code f) (value x)
    code (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
      inline' (VarMap.insert binder x map) body
    code (ReturnCode val) = returns (value val)
    code (GlobalCode g) = global g
    code (ThrowCode x f) = throw (value x) (code f)
    code (CatchCode binder@(Variable (StackType t) _) body) = catch t $ \x ->
      inline' (VarMap.insert binder x map) body
    value :: Data x -> DataBuilder x
    value (VariableData variable) =
      let Just replacement = VarMap.lookup variable map
       in replacement
    value (ConstantData k) = constant k
