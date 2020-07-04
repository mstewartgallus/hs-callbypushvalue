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
  KontCode :: Variable (Stack a) -> Code R -> Code a
  JumpEffect :: Code a -> Data (Stack a) -> Code R

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  LetToStackData :: Variable a -> Code R -> Data (Stack (F a))

instance TextShow (Code a) where
  showb (GlobalCode k) = showb k
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode x) = fromString "return " <> showb x
  showb (LambdaCode k body) = fromString "λ " <> showb k <> fromString " →\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (KontCode k body) = fromString "κ " <> showb k <> fromString " →\n" <> showb body
  showb (JumpEffect action stack) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb action))) <> fromString "\n}\n" <> showb stack

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (LetToStackData binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body

newtype CodeBuilder a = CodeBuilder {build :: Unique.Stream -> Code a}

newtype DataBuilder a = DataBuilder {buildData :: Unique.Stream -> Data a}

jump :: CodeBuilder a -> DataBuilder (Stack a) -> CodeBuilder R
jump x f = CodeBuilder $ \(Unique.Split l r) ->
  JumpEffect (build x l) (buildData f r)

kont :: Type a -> (DataBuilder (Stack a) -> CodeBuilder R) -> CodeBuilder a
kont t f = CodeBuilder $ \(Unique.Pick h stream) ->
  let v = Variable (ApplyType stack t) h
      body = build (f ((DataBuilder . const) $ VariableData v)) stream
   in KontCode v body

global :: Global a -> CodeBuilder a
global g = (CodeBuilder . const) $ GlobalCode g

returns :: DataBuilder a -> CodeBuilder (F a)
returns value = CodeBuilder $ \stream ->
  ReturnCode (buildData value stream)

letTo :: Type a -> (DataBuilder a -> CodeBuilder R) -> DataBuilder (Stack (F a))
letTo t f = DataBuilder $ \(Unique.Pick h (Unique.Split l r)) ->
  let v = Variable t h
      body = build (f ((DataBuilder . const) $ VariableData v)) r
   in LetToStackData v body

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

typeOfData :: Data a -> Type a
typeOfData (ConstantData (IntegerConstant _)) = intRaw
typeOfData (VariableData (Variable t _)) = t

simplify :: Code a -> Code a
simplify (LambdaCode binder body) = LambdaCode binder (simplify body)
simplify (ApplyCode f x) = ApplyCode (simplify f) x
simplify (LetBeCode thing binder body) = LetBeCode thing binder (simplify body)
simplify (KontCode _ _) = undefined
simplify (JumpEffect _ _) = undefined
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
    code (JumpEffect x f) = jump (code x) (value f)
    value :: Data x -> DataBuilder x
    value (VariableData variable) =
      let Just replacement = VarMap.lookup variable map
       in replacement
    value (ConstantData k) = constant k

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0

evaluate :: Code (F a) -> (a -> IO ()) -> IO ()
evaluate code k = interpret VarMap.empty code (PopStack k)

newtype Id a = Id a

interpretData :: VarMap Id -> Data a -> a
interpretData _ (ConstantData k) = interpretConstant k
interpretData values (VariableData v) = case VarMap.lookup v values of
  Just (Id x) -> x
interpretData env (LetToStackData binder body) = PopStack $ \value ->
  interpretEffect (VarMap.insert binder (Id value) env) body

interpret :: VarMap Id -> Code a -> Stack a -> IO ()
interpret values (ReturnCode value) (PopStack k) =
  let value' = interpretData values value
   in k value'
interpret values (ApplyCode f x) k = interpret values f (PushStack (interpretData values x) k)
interpret env (LetBeCode value binder body) k =
  let value' = interpretData env value
      env' = VarMap.insert binder (Id value') env
   in interpret env' body k
interpret values (KontCode variable body) k =
  let values' = VarMap.insert variable (Id k) values
   in interpretEffect values' body
interpret values (LambdaCode variable body) (PushStack head tail) =
  let values' = VarMap.insert variable (Id head) values
   in interpret values' body tail
interpret values (GlobalCode global) k =
  let Just (X g) = GlobalMap.lookup global globals
   in g k

data X a = X (Stack a -> IO ())

globals :: GlobalMap X
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus (X strictPlusImpl)
    ]

strictPlusImpl :: Stack (Integer -> Integer -> F Integer) -> IO ()
strictPlusImpl (PushStack x (PushStack y (PopStack k))) = k (x + y)

interpretEffect :: VarMap Id -> Code R -> IO ()
interpretEffect values (JumpEffect ip stack) =
  let stack' = interpretData values stack
   in interpret values ip stack'

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
