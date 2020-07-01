{-# LANGUAGE GADTs, TypeOperators #-}
module Callcc (Action (..), Thing (..), simplify) where
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

data AnyAction where
  AnyAction :: Action a -> AnyAction

data AnyThing where
  AnyThing :: Thing a -> AnyThing

instance Eq AnyAction where
  AnyAction (GlobalAction g) == AnyAction (GlobalAction g') = AnyGlobal g == AnyGlobal g'
  AnyAction (LambdaAction binder body) == AnyAction (LambdaAction binder' body') = AnyVariable binder == AnyVariable binder' && AnyAction body == AnyAction body'
  AnyAction (LetBeAction value binder body) == AnyAction (LetBeAction value' binder' body') = AnyThing value == AnyThing value' && AnyVariable binder' == AnyVariable binder' && AnyAction body == AnyAction body'
  AnyAction (LetToAction act binder body) == AnyAction (LetToAction act' binder' body') = AnyAction act == AnyAction act' && AnyVariable binder' == AnyVariable binder' && AnyAction body == AnyAction body'
  AnyAction (ApplyAction f x) == AnyAction (ApplyAction f' x') = AnyAction f == AnyAction f' && AnyThing x == AnyThing x'
  AnyAction (ReturnAction x) == AnyAction (ReturnAction x') = AnyThing x == AnyThing x'
  AnyAction (CatchAction binder body) == AnyAction (CatchAction binder' body') = AnyVariable binder == AnyVariable binder' && AnyAction body == AnyAction body'
  AnyAction (ThrowAction stack body) == AnyAction (ThrowAction stack' body') = AnyThing stack == AnyThing stack' && AnyAction body == AnyAction body'
  _ == _ = False

instance Eq AnyThing where
  AnyThing (ConstantThing k) == AnyThing (ConstantThing k') = AnyConstant k == AnyConstant k'
  AnyThing (VariableThing v) == AnyThing (VariableThing v') = AnyVariable v == AnyVariable v'
  _ == _ = False

instance Eq (Action a) where
  x == y = AnyAction x == AnyAction y

instance Eq (Thing a) where
  x == y = AnyThing x == AnyThing y

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

simplify :: Action a -> Action a
simplify (LetToAction (ReturnAction value) binder body) = simplify (LetBeAction value binder body)

simplify (LambdaAction binder body) = LambdaAction binder (simplify body)
simplify (ApplyAction f x) = ApplyAction (simplify f) x
simplify (LetBeAction thing binder body) = LetBeAction thing binder (simplify body)
simplify (LetToAction act binder body) = LetToAction (simplify act) binder (simplify body)
simplify (CatchAction binder body) = CatchAction binder (simplify body)
simplify (ThrowAction stack act) = ThrowAction stack (simplify act)
simplify x = x
