{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Code (..), Data (..), Builder (..), simplify, inline, evaluate, typeOf) where

import Common
import Core
import qualified Data.Text as T
import GlobalMap (GlobalMap)
import qualified GlobalMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Unique
import VarMap (VarMap)
import qualified VarMap

data Code a where
  GlobalCode :: Global a -> Code a
  ReturnCode :: Data a -> Code (F a)
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  JumpCode :: Code a -> Data (Stack a) -> Code Nil

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  LetToData :: Variable a -> Code Nil -> Data (Stack (F a))
  PushData :: Data a -> Data (Stack b) -> Data (Stack (a -> b))
  NilStackData :: Data (Stack Nil)

class Cps t where
  constant :: Constant a -> t Data a
  global :: Global a -> t Code a
  returns :: t Data a -> t Code (F a)
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b
  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a -> b)

  letTo :: Type a -> (t Data a -> t Code Nil) -> t Data (Stack (F a))
  push :: t Data a -> t Data (Stack b) -> t Data (Stack (a -> b))

  nilStack :: t Data (Stack Nil)
  jump :: t Code a -> t Data (Stack a) -> t Code Nil

instance Cps Builder where
  global g = (Builder . pure) $ GlobalCode g
  returns value =
    Builder $
      pure ReturnCode <*> builder value
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOfData x'
    h <- Unique.uniqueId
    let v = Variable t h
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LetBeCode x' v body
  lambda t f = Builder $ do
    h <- Unique.uniqueId
    let v = Variable t h
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LambdaCode v body
  constant k = (Builder . pure) $ ConstantData k

  letTo t f = Builder $ do
    h <- Unique.uniqueId
    let v = Variable t h
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ LetToData v body

  jump x f = Builder $ do
    x' <- builder x
    f' <- builder f
    pure $ JumpCode x' f'

  nilStack = Builder $ pure $ NilStackData
  push x k = Builder $ do
    x' <- builder x
    k' <- builder k
    pure $ PushData x' k'

instance TextShow (Code a) where
  showb (GlobalCode k) = showb k
  showb (ReturnCode x) = fromString "return " <> showb x
  showb (LambdaCode k body) = fromString "λ " <> showb k <> fromString " →\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (JumpCode action stack) = showb action <> fromString " , " <> showb stack

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (LetToData binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body
  showb (PushData x f) = showb x <> fromString " :: " <> showb f

build :: Builder t a -> t a
build (Builder s) = Unique.run s

newtype Builder t a = Builder {builder :: Unique.State (t a)}

typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t
typeOf (LambdaCode (Variable t _) body) = t -=> typeOf body
typeOf (ReturnCode value) = applyType returnsType (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body

typeOfData :: Data a -> Type a
typeOfData (ConstantData (IntegerConstant _)) = intRaw
typeOfData (VariableData (Variable t _)) = t
typeOfData (LetToData (Variable t _) _) = applyType stack $ applyType returnsType t

simplify :: Data a -> Data a
simplify = simpData

simpData :: Data a -> Data a
simpData (LetToData binder body) = LetToData binder (simpCode body)
simpData (PushData head tail) = PushData (simpData head) (simpData tail)
simpData x = x

simpCode :: Code a -> Code a
simpCode (LambdaCode binder body) = LambdaCode binder (simpCode body)
simpCode (LetBeCode thing binder body) = LetBeCode (simpData thing) binder (simpCode body)
simpCode (JumpCode x f) = JumpCode (simpCode x) (simpData f)
simpCode (ReturnCode value) = ReturnCode (simpData value)
simpCode g@(GlobalCode _) = g

inline :: Data a -> Builder Data a
inline = inlineData VarMap.empty

newtype Y a = Y (Builder Data a)

inlineData :: VarMap Y -> Data a -> Builder Data a
inlineData env (VariableData variable) =
  let Just (Y replacement) = VarMap.lookup variable env
   in replacement
inlineData env (LetToData binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (Y value) env
   in inlineCode env' body
inlineData env (PushData head tail) = Cps.push (inlineData env head) (inlineData env tail)
inlineData _ (ConstantData k) = Cps.constant k

inlineCode :: VarMap Y -> Code x -> Builder Code x
inlineCode env (LetBeCode term binder body) =
  if count binder body <= 1
    then inlineCode (VarMap.insert binder (Y (inlineData env term)) env) body
    else letBe (inlineData env term) $ \x ->
      inlineCode (VarMap.insert binder (Y x) env) body
inlineCode env (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
  inlineCode (VarMap.insert binder (Y x) env) body
inlineCode env (ReturnCode val) = returns (inlineData env val)
inlineCode _ (GlobalCode g) = global g
inlineCode env (JumpCode x f) = jump (inlineCode env x) (inlineData env f)

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (JumpCode x f) = code x + value f
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (LetToData binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    value (PushData head tail) = value head + value tail
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0

evaluate :: Data a -> a
evaluate = interpretData VarMap.empty

newtype Id a = Id a

interpretData :: VarMap Id -> Data a -> a
interpretData _ (ConstantData k) = interpretConstant k
interpretData env (VariableData v) = case VarMap.lookup v env of
  Just (Id x) -> x
interpretData env (LetToData binder body) = PopStack $ \value ->
  let env' = VarMap.insert binder (Id value) env
   in interpret env' body NilStack
interpretData env (PushData h t) =
  let h' = interpretData env h
      t' = interpretData env t
   in PushStack h' t'

interpret :: VarMap Id -> Code a -> Stack a -> R
interpret values (ReturnCode value) (PopStack k) =
  let value' = interpretData values value
   in k value'
interpret env (LetBeCode value binder body) k =
  let value' = interpretData env value
      env' = VarMap.insert binder (Id value') env
   in interpret env' body k
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
