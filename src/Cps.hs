{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Cps (Code (..), Data (..), CodeBuilder (..), DataBuilder (..), build, simplify, inline, evaluate, typeOf, jump, kont, global, apply, returns, lambda, letBe, constant, letTo) where

import Common
import Core
import qualified Data.Text as T
import GlobalMap (GlobalMap)
import qualified GlobalMap
import TextShow
import Unique
import VarMap (VarMap)
import qualified VarMap

data Code a where
  GlobalCode :: Global a -> Code a
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  KontCode :: Variable (Stack a) -> Code Nil -> Code a
  JumpCode :: Code a -> Data (Stack a) -> Code Nil

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a

instance TextShow (Code a) where
  showb (GlobalCode k) = showb k
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode x) = fromString "return " <> showb x
  showb (LambdaCode k body) = fromString "λ " <> showb k <> fromString " →\n" <> showb body
  showb (LetToCode value binder body) = showb value <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (KontCode k body) = fromString "κ " <> showb k <> fromString " →\n" <> showb body
  showb (JumpCode action stack) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb action))) <> fromString "\n}\n" <> showb stack

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v

newtype CodeBuilder a = CodeBuilder {build :: Unique.Stream -> Code a}

newtype DataBuilder a = DataBuilder {buildData :: Unique.Stream -> Data a}

jump :: CodeBuilder a -> DataBuilder (Stack a) -> CodeBuilder Nil
jump x f = CodeBuilder $ \(Unique.Split l r) ->
  JumpCode (build x l) (buildData f r)

kont :: Type a -> (DataBuilder (Stack a) -> CodeBuilder Nil) -> CodeBuilder a
kont t f = CodeBuilder $ \(Unique.Pick h stream) ->
  let v = Variable (ApplyType stack t) h
      body = build (f ((DataBuilder . const) $ VariableData v)) stream
   in KontCode v body

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

constant :: Constant a -> DataBuilder a
constant k = (DataBuilder . const) $ ConstantData k

typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t
typeOf (LambdaCode (Variable t _) body) = t -=> typeOf body
typeOf (ReturnCode value) = ApplyType returnsType (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LetToCode _ _ body) = typeOf body
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result
typeOf (KontCode (Variable (StackType t) _) _) = t

typeOfData :: Data a -> Type a
typeOfData (ConstantData (IntegerConstant _)) = intRaw
typeOfData (VariableData (Variable t _)) = t

simplify :: Code a -> Code a
simplify (LetToCode (ReturnCode value) binder body) = simplify (LetBeCode value binder body)
simplify (LambdaCode binder body) = LambdaCode binder (simplify body)
simplify (ApplyCode f x) = ApplyCode (simplify f) x
simplify (LetToCode act binder body) = LetToCode (simplify act) binder (simplify body)
simplify (LetBeCode thing binder body) = LetBeCode thing binder (simplify body)
simplify (KontCode _ _) = undefined
simplify (JumpCode _ _) = undefined
simplify x = x

inline :: Code a -> CodeBuilder a
inline = inline' VarMap.empty

inline' :: VarMap DataBuilder -> Code a -> CodeBuilder a
inline' map = code
  where
    code :: Code x -> CodeBuilder x
    code (LetBeCode term binder body) =
      if count binder body <= 1
        then inline' (VarMap.insert binder (value term) map) body
        else letBe (value term) $ \x ->
          inline' (VarMap.insert binder x map) body
    code (ApplyCode f x) = apply (code f) (value x)
    code (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
      inline' (VarMap.insert binder x map) body
    code (ReturnCode val) = returns (value val)
    code (GlobalCode g) = global g
    code (KontCode binder@(Variable (StackType t) _) body) = kont t $ \x ->
      inline' (VarMap.insert binder x map) body
    code (JumpCode x f) = jump (code x) (value f)
    value :: Data x -> DataBuilder x
    value (VariableData variable) =
      let Just replacement = VarMap.lookup variable map
       in replacement
    value (ConstantData k) = constant k

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (KontCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (JumpCode x f) = code x + value f
    code (LetToCode x binder body) = code x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0

evaluate :: Code (F a) -> (a -> IO ()) -> IO ()
evaluate code k =
  let R eff = interpret VarMap.empty code (PopStack (\x -> R (k x)))
   in eff

newtype Id a = Id a

interpretData :: VarMap Id -> Data a -> a
interpretData _ (ConstantData k) = interpretConstant k
interpretData values (VariableData v) = case VarMap.lookup v values of
  Just (Id x) -> x

interpret :: VarMap Id -> Code a -> Stack a -> R
interpret values (ReturnCode value) (PopStack k) =
  let value' = interpretData values value
   in k value'
interpret values (ApplyCode f x) k = interpret values f (PushStack (interpretData values x) k)
interpret env (LetBeCode value binder body) k =
  let value' = interpretData env value
      env' = VarMap.insert binder (Id value') env
   in interpret env' body k
interpret env (LetToCode action binder body) k =
  interpret
    env
    action
    ( PopStack $ \value ->
        let env' = VarMap.insert binder (Id value) env
         in interpret env' body k
    )
interpret values (KontCode variable body) k =
  let values' = VarMap.insert variable (Id k) values
   in interpret values' body NilStack
interpret values (LambdaCode variable body) (PushStack head tail) =
  let values' = VarMap.insert variable (Id head) values
   in interpret values' body tail
interpret values (GlobalCode global) k =
  let Just (X g) = GlobalMap.lookup global globals
   in g k
interpret env (JumpCode x f) NilStack =
  let stack = interpretData env f
   in interpret env x stack

data X a = X (Stack a -> R)

globals :: GlobalMap X
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus (X strictPlusImpl)
    ]

strictPlusImpl :: Stack (Integer -> Integer -> F Integer) -> R
strictPlusImpl (PushStack x (PushStack y (PopStack k))) = k (x + y)

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
