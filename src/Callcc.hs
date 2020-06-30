{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Callcc (Action (..) ) where
import Common
import TextShow

data Action a where
  ConstantAction :: Constant a -> Action a
  GlobalAction :: Global a -> Action a
  LambdaAction :: Variable a -> Action b -> Action (a -> b)
  ApplyAction :: Action (a -> b) -> Variable a -> Action b
  ReturnAction :: Variable a -> Action (F a)
  LetBeAction :: Variable a -> Variable a -> Action b -> Action b
  LetToAction :: Action (F a) -> Variable a -> Action b -> Action b
  CatchAction :: Variable (Stack a) -> Action a -> Action a
  ThrowAction :: Variable (Stack a) -> Action a -> Action b

instance TextShow (Action a) where
  showb (ConstantAction k) = showb k
  showb (GlobalAction g) = showb g
  showb (LambdaAction binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyAction f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnAction value) = fromString "return " <> showb value
  showb (LetToAction action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeAction value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchAction binder body) = fromString "catch " <> showb binder <> fromString ".\n" <> showb body
  showb (ThrowAction label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body
