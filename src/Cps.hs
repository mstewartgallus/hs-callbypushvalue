{-# LANGUAGE GADTs, TypeOperators #-}
module Cps (Code (..), Data (..), Effect (..), evaluate) where
import Common
import TextShow
import qualified Data.Text as T
import VarMap (VarMap)
import qualified VarMap
import LabelMap (LabelMap)
import qualified LabelMap

data Code a where
  GlobalCode :: Global a -> Code a
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  KontCode :: Variable (Stack a) -> Effect -> Code a

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  LetToStackData :: Variable a -> Effect -> Data (Stack (F a))

data Effect where
  JumpEffect :: Code a -> Data (Stack a) -> Effect

instance TextShow (Code a) where
  showb (GlobalCode k) = showb k
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode x) = fromString "return " <> showb x
  showb (LambdaCode k body) = fromString "λ " <> showb k <> fromString " →\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (KontCode k body) = fromString "κ " <> showb k <> fromString " →\n" <> showb body

instance TextShow (Data a) where
 showb (ConstantData k) = showb k
 showb (VariableData v) = showb v
 showb (LetToStackData binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body

instance TextShow Effect where
 showb (JumpEffect action stack) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb action))) <> fromString "\n}\n" <> showb stack


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
-- interpret values (LetBeCode value binder body) k = let
--   values' = VarMap.insert variable (Id head) values
--   in interpret values' body tail

interpretEffect :: VarMap Id -> Effect -> IO ()
interpretEffect values (JumpEffect ip stack) = let
  stack' = interpretData values stack
  in interpret values ip stack'

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
