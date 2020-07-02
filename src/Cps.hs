{-# LANGUAGE GADTs, TypeOperators #-}
module Cps (Code (..), Data (..), Effect (..)) where
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
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  KontCode :: Variable (Stack a) -> Effect -> Code a

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a

data Effect where
  JumpEffect :: Code a -> Data (Stack a) -> Effect

instance TextShow (Code a) where
  showb (GlobalCode k) = showb k
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode x) = fromString "return " <> showb x
  showb (LambdaCode k body) = fromString "λ " <> showb k <> fromString " →\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (KontCode k body) = fromString "κ " <> showb k <> fromString " →\n" <> showb body

instance TextShow (Data a) where
 showb (ConstantData k) = showb k
 showb (VariableData v) = showb v

instance TextShow Effect where
 showb (JumpEffect action stack) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb action))) <> fromString "\n}\n" <> showb stack

newtype Id a = Id a

interpretData :: LabelMap Id -> VarMap Id -> Data a -> a
interpretData _ _ (ConstantData k) = interpretConstant k
interpretData _ values (VariableData v) = case VarMap.lookup v values of
  Just (Id x) -> x

interpret :: LabelMap Id -> VarMap Id -> Code a -> Stack a -> IO ()
interpret labels values (ReturnCode value) (PopStack k) = let
  value' = interpretData labels values value
  in k value'
-- interpret labels values (LambdaCode variable body) (PushStack head tail) = let
--   values' = VarMap.insert variable (Id tail) values
--   PopStack body' = interpretData labels values' body
--   in body' head
interpret labels values (KontCode variable body) k = let
  values' = VarMap.insert variable (Id k) values
  in interpretEffect labels values' body

interpretEffect :: LabelMap Id ->VarMap Id -> Effect -> IO ()
interpretEffect labels values (JumpEffect ip stack) = let
  stack' = interpretData labels values stack
  in interpret labels values ip stack'

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
