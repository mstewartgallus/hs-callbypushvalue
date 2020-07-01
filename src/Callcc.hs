{-# LANGUAGE GADTs, TypeOperators #-}
module Callcc (Action (..), Thing (..)) where
import Common
import TextShow

data Action a where
  GlobalAction :: Global a -> Action a
  LambdaAction :: Variable a -> Action b -> Action (a -> b)
  ApplyAction :: Action (a -> b) -> Thing a -> Action b
  ReturnAction :: Thing a -> Action (F a)
  LetBeAction :: Thing a -> Variable a -> Action b -> Action b
  LetToAction :: Action (F a) -> Variable a -> Action b -> Action b
  CatchAction :: Variable (Stack a) -> Action a -> Action a
  ThrowAction :: Thing (Stack a) -> Action a -> Action b

data Thing a where
  ConstantThing :: Constant a -> Thing a
  VariableThing :: Variable a -> Thing a

instance TextShow (Action a) where
  showb (GlobalAction g) = showb g
  showb (LambdaAction binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyAction f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnAction value) = fromString "return " <> showb value
  showb (LetToAction action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeAction value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchAction binder body) = fromString "catch " <> showb binder <> fromString ".\n" <> showb body
  showb (ThrowAction label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body

instance TextShow (Thing a) where
  showb (ConstantThing k) = showb k
  showb (VariableThing b) = showb b
