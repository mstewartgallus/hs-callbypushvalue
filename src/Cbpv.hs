{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Cbpv (Code (..), Value (..)) where
import Common
import TextShow
import qualified Data.Text as T

data Code a where
  ConstantCode :: Constant a -> Code a
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Value a -> Code b
  ForceCode :: Value (U a) -> Code a
  ReturnCode :: Value a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Value a -> Variable a -> Code b -> Code b

data Value a where
  VariableValue :: Variable a -> Value a
  ThunkValue :: Code a -> Value (U a)


instance TextShow (Code a) where
  showb (ConstantCode k) = showb k
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ForceCode thunk) = fromString "! " <> showb thunk
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body

instance TextShow (Value a) where
  showb (VariableValue v) = showb v
  showb (ThunkValue code) = fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb code))) <> fromString "\n}"
