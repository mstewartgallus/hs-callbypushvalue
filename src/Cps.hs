{-# LANGUAGE GADTs, TypeOperators #-}
module Cps (Code (..), Data (..), evaluate) where
import Common
import Core
import TextShow
import qualified Data.Text as T
import VarMap (VarMap)
import qualified VarMap
import GlobalMap (GlobalMap)
import qualified GlobalMap

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




typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t

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
interpret values (ReturnCode value) (PopStack k) = let
  value' = interpretData values value
  in k value'
interpret values (ApplyCode f x) k = interpret values f (PushStack (interpretData values x) k)
interpret env (LetBeCode value binder body) k = let
  value' = interpretData env value
  env' = VarMap.insert binder (Id value') env
  in interpret env' body k
interpret values (KontCode variable body) k = let
  values' = VarMap.insert variable (Id k) values
  in interpretEffect values' body
interpret values (LambdaCode variable body) (PushStack head tail) = let
  values' = VarMap.insert variable (Id head) values
  in interpret values' body tail
interpret values (GlobalCode global) k = let
  Just (X g) = GlobalMap.lookup global globals
  in g k

data X a = X (Stack a -> IO ())
globals :: GlobalMap X
globals = GlobalMap.fromList [
  GlobalMap.Entry strictPlus (X strictPlusImpl)
                             ]
strictPlusImpl :: Stack (Integer -> Integer -> F Integer) -> IO ()
strictPlusImpl (PushStack x (PushStack y (PopStack k))) = k (x + y)

interpretEffect :: VarMap Id -> Code R -> IO ()
interpretEffect values (JumpEffect ip stack) = let
  stack' = interpretData values stack
  in interpret values ip stack'

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
