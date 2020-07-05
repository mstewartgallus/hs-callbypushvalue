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
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  KontCode :: Variable (Stack a) -> Code Nil -> Code a
  JumpCode :: Code a -> Data (Stack a) -> Code Nil

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  LetToStackData :: Variable a -> Code Nil -> Data (Stack (F a))
  PushStackData :: Data a -> Data (Stack b) -> Data (Stack (a -> b))

class Cps t where
  constant :: Constant a -> t Data a
  global :: Global a -> t Code a
  returns :: t Data a -> t Code (F a)
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b
  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a -> b)
  apply :: t Code (a -> b) -> t Data a -> t Code b
  letTo :: Type a -> (t Data a -> t Code Nil) -> t Data (Stack (F a))
  kont :: Type a -> (t Data (Stack a) -> t Code Nil) -> t Code a
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
  apply f x = Builder $ do
    f' <- builder f
    x' <- builder x
    pure $ ApplyCode f' x'
  constant k = (Builder . pure) $ ConstantData k
  jump x f = Builder $ do
    x' <- builder x
    f' <- builder f
    pure $ JumpCode x' f'
  kont t f = Builder $ do
    h <- Unique.uniqueId
    let v = Variable (ApplyType stack t) h
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ KontCode v body
  letTo t f = Builder $ do
    h <- Unique.uniqueId
    let v = Variable t h
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LetToStackData v body

instance TextShow (Code a) where
  showb (GlobalCode k) = showb k
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode x) = fromString "return " <> showb x
  showb (LambdaCode k body) = fromString "λ " <> showb k <> fromString " →\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (KontCode k body) = fromString "κ " <> showb k <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString " → {\n" <> showb body))) <> fromString "\n}"
  showb (JumpCode action stack) = showb action <> fromString "\n" <> showb stack

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (LetToStackData binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body
  showb (PushStackData h t) = fromString "push " <> showb h <> fromString ".\n" <> showb t

build :: Builder t a -> t a
build (Builder s) = Unique.run s

newtype Builder t a = Builder {builder :: Unique.State (t a)}

typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t
typeOf (LambdaCode (Variable t _) body) = t -=> typeOf body
typeOf (ReturnCode value) = ApplyType returnsType (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result
typeOf (KontCode (Variable (StackType t) _) _) = t

typeOfData :: Data a -> Type a
typeOfData (ConstantData (IntegerConstant _)) = intRaw
typeOfData (VariableData (Variable t _)) = t

simplify :: Code a -> Code a
simplify (ApplyCode (LambdaCode binder body) value) = simplify (LetBeCode value binder body)
simplify (JumpCode (KontCode binder body) value) = simplify (LetBeCode value binder body)
simplify (LambdaCode binder body) = LambdaCode binder (simplify body)
simplify (ApplyCode f x) = ApplyCode (simplify f) x
simplify (LetBeCode thing binder body) = LetBeCode thing binder (simplify body)
simplify (KontCode binder body) = KontCode binder (simplify body)
simplify (JumpCode x f) = JumpCode (simplify x) f
simplify g@(GlobalCode _) = g
simplify r@(ReturnCode _) = r

inline :: Code a -> Builder Code a
inline = inline' VarMap.empty

newtype Y a = Y (Builder Data a)

inline' :: VarMap Y -> Code a -> Builder Code a
inline' map = code
  where
    code :: Code x -> Builder Code x
    code (LetBeCode term binder body) =
      if count binder body <= 1
        then inline' (VarMap.insert binder (Y (value term)) map) body
        else letBe (value term) $ \x ->
          inline' (VarMap.insert binder (Y x) map) body
    code (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
      inline' (VarMap.insert binder (Y x) map) body
    code (ReturnCode val) = returns (value val)
    code (GlobalCode g) = global g
    code (KontCode binder@(Variable (StackType t) _) body) = kont t $ \x ->
      inline' (VarMap.insert binder (Y x) map) body
    code (JumpCode x f) = jump (code x) (value f)
    code (ApplyCode f x) = apply (code f) (value x)
    value :: Data x -> Builder Data x
    value (VariableData variable) =
      let Just (Y replacement) = VarMap.lookup variable map
       in replacement
    value (ConstantData k) = constant k
    value (LetToStackData binder@(Variable t _) body) = letTo t $ \x ->
      inline' (VarMap.insert binder (Y x) map) body

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (KontCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (JumpCode x f) = code x + value f
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (LetToStackData binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    value _ = 0

evaluate :: Code (F a) -> (a -> IO ()) -> IO ()
evaluate code k =
  let R eff = interpret VarMap.empty code (PopStack (\x -> R (k x)))
   in eff

newtype Id a = Id a

interpretData :: VarMap Id -> Data a -> a
interpretData _ (ConstantData k) = interpretConstant k
interpretData env (LetToStackData binder body) = PopStack $ \value ->
  interpret (VarMap.insert binder (Id value) env) body NilStack
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
