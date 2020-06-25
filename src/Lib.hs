{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Lib
    (
      fn, thunk, int, plus,
      Term (
        VariableTerm, ApplyTerm, LambdaTerm, ConstantTerm
           ),
      Variable (Variable ),
      Constant (IntegerConstant ),
      Global (Global ),
      Type (), Code (), Action (), Stuff (), Stack (), F (), U (), (:->) (),
      CompilerState (CompilerState), Compiler (),
      toCallByPushValue, toExplicitCatchThrow, toCps',
      intrinsify, simplifyCpbv
    ) where

import Control.Monad.State

import qualified Data.Text as T

import TextShow

import Data.Map (Map)
import qualified Data.Map as Map

import Unsafe.Coerce

{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}

fn :: Type (V a (V b (a :-> b)))
fn = NominalType (T.pack "core") (T.pack "fn")

thunk :: Type (V a (U a))
thunk = NominalType (T.pack "core") (T.pack "U")

returns :: Type (V a (F a))
returns = NominalType (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = ApplyType returns intRaw

intRaw :: Type Integer
intRaw = NominalType (T.pack "core") (T.pack "int")

plus :: Term (F Integer :-> F Integer :-> F Integer)
plus = GlobalTerm (Global (ApplyType (ApplyType fn int) (ApplyType (ApplyType fn int) int)) (T.pack "core") (T.pack "+"))

strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global undefined (T.pack "core") (T.pack "+!")



{-
Simplify Call By Push Value Inverses

So far we handle:

- force (thunk X) to X
- thunk (force X) to X
-}

data V a b

type a :-> b = U a -> b
infixr 9 :->

data Type a where
  NominalType :: T.Text -> T.Text -> Type a
  ApplyType :: Type (V a b) -> Type a -> Type b



data Variable a = Variable (Type a) T.Text
instance Eq (Variable a) where
  (Variable _ x) == (Variable _ y) = x == y

instance Ord (Variable a) where
  compare (Variable _ x) (Variable _ y) = compare x y


data Label a = Label (Type a) T.Text
data Constant a where
  IntegerConstant :: Integer -> Constant (F Integer)
data Global a = Global (Type a) T.Text T.Text



data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term a
  GlobalTerm :: Global a -> Term a
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b



data F a
type U a = Stack (F (Stack a))

data Code a where
  ConstantCode :: Constant a -> Code a
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Value a -> Code b
  ForceCode :: Value (U a) -> Code a
  ReturnCode :: Value a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b

data Value a where
  VariableValue :: Variable a -> Value a
  ThunkValue :: Code a -> Value (U a)



data Stack a

data Action a where
  ConstantAction :: Constant a -> Action a
  GlobalAction :: Global a -> Action a
  LambdaAction :: Variable a -> Action b -> Action (a -> b)
  ApplyAction :: Action (a -> b) -> Variable a -> Action b
  ReturnAction :: Variable a -> Action (F a)
  LetToAction :: Action (F a) -> Variable a -> Action b -> Action b
  CatchAction :: Variable (Stack a) -> Action a -> Action a
  ThrowAction :: Variable (Stack a) -> Action a -> Action b



data Does a where
  ConstantDoes :: Constant a -> Does a
  GlobalDoes :: Global a -> Does a
  ApplyDoes :: Does (a -> b) -> Stuff a -> Does b
  ReturnDoes :: Stuff a -> Does (F a)
  LabelDoes :: Label a -> Does a
  LambdaDoes :: Variable (Stack b) -> Stuff (Stack (F a)) -> Does (a -> b)

data Stuff a where
  VariableStuff :: Variable a -> Stuff a
  ToStackStuff :: Variable a -> Effect -> Stuff (Stack (F a))
  LabelStackStuff :: Label a -> Effect -> Stuff (Stack a)

data Effect where
  JumpEffect :: Does a -> Stuff (Stack a) -> Effect



thunkify :: Variable a -> Variable (U a)
thunkify (Variable t name) = Variable (ApplyType thunk t) name

toCallByPushValue :: Term a -> Code a
toCallByPushValue (VariableTerm x) = ForceCode (VariableValue (thunkify x))
toCallByPushValue (ConstantTerm x) = ConstantCode x
toCallByPushValue (GlobalTerm x) = GlobalCode x
toCallByPushValue (LambdaTerm binder body) = LambdaCode (thunkify binder) (toCallByPushValue body)
toCallByPushValue (ApplyTerm f x) = ApplyCode (toCallByPushValue f) (ThunkValue (toCallByPushValue x))



data CompilerState = CompilerState Integer Integer
type Compiler = State CompilerState

getVariable :: Type a -> Compiler (Variable a)
getVariable t = do
  CompilerState n m <- get
  put (CompilerState (n + 1) m)
  pure (Variable t (toText (fromString "v_" <> showb n)))

getLabel :: Type a -> Compiler (Label a)
getLabel t = do
  CompilerState n m <- get
  put (CompilerState n (m + 1))
  pure (Label t (toText (fromString "l_" <> showb m)))



toExplicitCatchThrow :: Code a -> Compiler (Action a)
toExplicitCatchThrow (ConstantCode x) = pure (ConstantAction x)
toExplicitCatchThrow (GlobalCode x) = pure (GlobalAction x)
toExplicitCatchThrow (LambdaCode binder body) = do
  body' <- toExplicitCatchThrow body
  pure (LambdaAction binder body')
toExplicitCatchThrow (ApplyCode f x) = do
  f' <- toExplicitCatchThrow f
  toExplicitCatchThrowValue x (\x' -> ApplyAction f' x')
toExplicitCatchThrow (LetToCode action binder body) = do
  action' <- toExplicitCatchThrow action
  body' <- toExplicitCatchThrow body
  return (LetToAction action' binder body')
toExplicitCatchThrow (ForceCode thunk) = do
  -- fixme...
  v <- getVariable undefined
  toExplicitCatchThrowValue thunk $ \thunk' -> CatchAction v (ThrowAction thunk' (ReturnAction v))

toExplicitCatchThrowValue :: Value a -> (Variable a -> Action b) -> Compiler (Action b)
toExplicitCatchThrowValue (VariableValue v) k = pure (k v)
toExplicitCatchThrowValue (ThunkValue code) k = do
  -- fixme...
  returner <- getVariable undefined
  label <- getVariable undefined
  binder <- getVariable undefined
  code' <- toExplicitCatchThrow code
  pure $ CatchAction returner $ LetToAction
      (CatchAction label (ThrowAction returner (k label)))
      binder
      (ThrowAction binder code')



toCps' :: Action a -> Compiler (Stuff (Stack (F (Stack a))))
toCps' act = do
  k <- getVariable undefined
  eff <- toCps act $ \act' -> do
    pure (JumpEffect act' (VariableStuff k))
  pure (ToStackStuff k eff)

toCps :: Action a -> (Does a -> Compiler Effect) -> Compiler Effect
toCps (ConstantAction x) k = k (ConstantDoes x)
toCps (GlobalAction x) k = k (GlobalDoes x)
toCps (ReturnAction value) k = k (ReturnDoes (VariableStuff value))
toCps (LambdaAction binder body) k = do
  tail <- getVariable undefined
  body' <- toCps body $ \b -> do
    pure (JumpEffect b (VariableStuff tail))

  k (LambdaDoes tail (ToStackStuff binder body'))
toCps (ApplyAction f x) k = do
  toCps f $ \f' -> k (ApplyDoes f' (VariableStuff x))
toCps (LetToAction action binder body) k = do
  toCps action $ \act -> do
      body' <- toCps body k
      pure (JumpEffect act (ToStackStuff binder body'))
toCps (CatchAction binder body) k = do
  -- fixme...
  label <- getLabel undefined
  body' <- toCps body $ \x -> do
      pure (JumpEffect x (VariableStuff binder))
  k' <- k (LabelDoes label)
  pure $ JumpEffect (ReturnDoes (LabelStackStuff label k')) $ ToStackStuff binder body'
toCps (ThrowAction binder body) _ = do
  toCps body $ \x -> do
      pure (JumpEffect x (VariableStuff binder))



instance TextShow (Variable a) where
  showb (Variable _ name) = fromText name
instance TextShow (Label a) where
  showb (Label _ name) = fromText name
instance TextShow (Constant a) where
  showb (IntegerConstant n) = showb n
instance TextShow (Global a) where
  showb (Global _ package name) = fromText package <> fromString "/" <> fromText name



instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LambdaTerm binder body) = fromString "(λ " <> showb binder <> fromString " → " <> showb body <> fromString ")"
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"



instance TextShow (Code a) where
  showb (ConstantCode k) = showb k
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ForceCode thunk) = fromString "! " <> showb thunk
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body

instance TextShow (Value a) where
  showb (VariableValue v) = showb v
  showb (ThunkValue code) = fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb code))) <> fromString "\n}"



instance TextShow (Action a) where
  showb (ConstantAction k) = showb k
  showb (GlobalAction g) = showb g
  showb (LambdaAction binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyAction f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnAction value) = fromString "return " <> showb value
  showb (LetToAction action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchAction binder body) = fromString "catch " <> showb binder <> fromString ".\n" <> showb body
  showb (ThrowAction label body) = fromString "throw " <> showb label <> fromString ".\n" <> showb body



instance TextShow (Does a) where
  showb (ConstantDoes k) = showb k
  showb (GlobalDoes k) = showb k
  showb (ApplyDoes f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnDoes x) = fromString "return " <> showb x
  showb (LabelDoes l) = showb l
  showb (LambdaDoes k body) = fromString "κ " <> showb k <> fromString " →\n" <> showb body

instance TextShow (Stuff a) where
 showb (VariableStuff v) = showb v
 showb (ToStackStuff binder effect) = fromString "to " <> showb binder <> fromString ".\n" <> showb effect
 showb (LabelStackStuff binder effect) = fromString "κ " <> showb binder <> fromString " →\n" <> showb effect

instance TextShow Effect where
 showb (JumpEffect action stack) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb action))) <> fromString "\n}\n" <> showb stack



intrinsify :: Code a -> Compiler (Code a)
intrinsify global@(GlobalCode (Global _ package name)) =
  if package /= T.pack "core"
  then pure global
  else if name == T.pack "+"
  -- fixme... do in a type safe way
  then do
    p <- plusIntrinsic
    pure (unsafeCoerce p)
  else pure global
intrinsify (LambdaCode binder x) = do
  x' <- intrinsify x
  pure $ LambdaCode binder x'
intrinsify (ApplyCode f x) = do
  f' <- intrinsify f
  x' <- intrinsifyValue x
  pure $ ApplyCode f' x'
intrinsify (ForceCode x) = do
  x' <- intrinsifyValue x
  pure $ ForceCode x'
intrinsify (ReturnCode x) = do
  x' <- intrinsifyValue x
  pure $ ReturnCode x'
intrinsify (LetToCode action binder body) = do
  action' <- intrinsify action
  body' <- intrinsify body
  pure $ LetToCode action' binder body'
intrinsify x = pure x

intrinsifyValue :: Value a -> Compiler (Value a)
intrinsifyValue (ThunkValue code) = do
   code' <- intrinsify code
   pure (ThunkValue code')
intrinsifyValue x = pure x

plusIntrinsic :: Compiler (Code (F Integer :-> F Integer :-> F Integer))
plusIntrinsic = do
  x <- getVariable int
  y <- getVariable int
  let x' = thunkify x
  let y' = thunkify y
  x'' <- getVariable intRaw
  y'' <- getVariable intRaw
  pure $
    LambdaCode x' $
    LambdaCode y' $
    LetToCode (ForceCode (VariableValue x')) x'' $
    LetToCode (ForceCode (VariableValue y')) y'' $
    ApplyCode (ApplyCode (GlobalCode strictPlus) (VariableValue x'')) (VariableValue y'')



{-
Simplify Call By Push Value Inverses

So far we handle:

- force (thunk X) to X
- thunk (force X) to X
-}
simplifyCpbv :: Code a -> Code a
simplifyCpbv (ForceCode (ThunkValue x)) = simplifyCpbv x
simplifyCpbv (ForceCode x) = ForceCode (simplifyCpbvValue x)
simplifyCpbv (LambdaCode binder body) = LambdaCode binder (simplifyCpbv body)
simplifyCpbv (ApplyCode f x) = ApplyCode (simplifyCpbv f) (simplifyCpbvValue x)
simplifyCpbv (ReturnCode value) = ReturnCode (simplifyCpbvValue value)
simplifyCpbv (LetToCode action binder body) = LetToCode (simplifyCpbv action) binder (simplifyCpbv body)
simplifyCpbv x = x

simplifyCpbvValue :: Value a -> Value a
simplifyCpbvValue (ThunkValue (ForceCode x)) = simplifyCpbvValue x
simplifyCpbvValue (ThunkValue x) = ThunkValue (simplifyCpbv x)
simplifyCpbvValue x = x
