{-# LANGUAGE GADTs, TypeOperators #-}
module Lib
    (
      fn, thunk, int, plus,
      Term (..),
      Variable (..),
      Constant (..),
      Global (Global ),
      Type (..), Code (), Action (), Stuff (), Stack (), F (), U (), (:->) (),
      CompilerState (..), Compiler,
      inlineTerm, simplifyTerm, toCallByPushValue, toExplicitCatchThrow, toCps',
      intrinsify, simplifyCbpv, inlineCbpv, simplifyCallcc
    ) where

import Control.Monad.State

import qualified Data.Text as T

import TextShow

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.ST
import Data.Typeable

import Core
import Common
import Compiler
import Callcc (Action (..), Thing (..))
import qualified Callcc
import Term (Term (..))
import qualified Term
import Cbpv (Code (..), Value (..))
import qualified Cbpv
import Cps

inlineTerm = Term.inline
simplifyTerm = Term.simplify
simplifyCbpv = Cbpv.simplify
inlineCbpv = Cbpv.inline
simplifyCallcc = Callcc.simplify
intrinsify = Cbpv.intrinsify

thunkify :: Variable a -> Variable (U a)
thunkify (Variable (Type t) name) = let
  Type thunk' = thunk
  in Variable (Type (ApplyName thunk' t)) name

toCallByPushValue :: Term a -> Compiler (Code a)
toCallByPushValue (VariableTerm x) = pure $ ForceCode (VariableValue x)
toCallByPushValue (ConstantTerm x) = pure $ ReturnCode (ConstantValue x)
toCallByPushValue (GlobalTerm x) = pure $ GlobalCode x
toCallByPushValue (LetTerm term t body) = do
  binder <- getVariable t
  term' <- toCallByPushValue term
  body' <- toCallByPushValue (body (VariableTerm binder))
  pure $ LetBeCode (ThunkValue term') binder body'
toCallByPushValue (LambdaTerm t body) = do
  binder <- getVariable t
  body' <- toCallByPushValue (body (VariableTerm binder))
  pure $ LambdaCode binder body'
toCallByPushValue (ApplyTerm f x) = do
  f' <- toCallByPushValue f
  x' <- toCallByPushValue x
  pure $ ApplyCode f' (ThunkValue x')



toExplicitCatchThrow :: Code a -> Compiler (Action a)
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
toExplicitCatchThrow (LetBeCode value binder body) = do
  body' <- toExplicitCatchThrow body
  toExplicitCatchThrowValue value $ \value' -> LetBeAction value' binder body'
toExplicitCatchThrow (ReturnCode x) = toExplicitCatchThrowValue x $ \x' -> ReturnAction x'
toExplicitCatchThrow (ForceCode thunk) = do
  -- fixme...
  v <- getVariable undefined
  toExplicitCatchThrowValue thunk $ \thunk' -> CatchAction v (ThrowAction thunk' (ReturnAction (VariableThing v)))

toExplicitCatchThrowValue :: Value a -> (Thing a -> Action b) -> Compiler (Action b)
toExplicitCatchThrowValue (ConstantValue x) k = pure (k (ConstantThing x))
toExplicitCatchThrowValue (VariableValue v) k = pure (k (VariableThing v))
toExplicitCatchThrowValue (ThunkValue code) k = do
  -- fixme...
  returner <- getVariable undefined
  label <- getVariable undefined
  binder <- getVariable undefined
  code' <- toExplicitCatchThrow code
  pure $ CatchAction returner $ LetToAction
      (CatchAction label (ThrowAction (VariableThing returner) (k (VariableThing label))))
      binder
      (ThrowAction (VariableThing binder) code')



toCps' :: Action a -> Compiler (Stuff (Stack (F (Stack a))))
toCps' act = do
  k <- getVariable undefined
  eff <- toCps act $ \act' -> do
    pure (JumpEffect act' (VariableStuff k))
  pure (ToStackStuff k eff)

toCps :: Action a -> (Cps a -> Compiler Effect) -> Compiler Effect
toCps (GlobalAction x) k = k (GlobalCps x)
toCps (ReturnAction value) k = k (ReturnCps (toCpsThing value))
toCps (LambdaAction binder body) k = do
  tail <- getVariable undefined
  body' <- toCps body $ \b -> do
    pure (JumpEffect b (VariableStuff tail))

  k (LambdaCps tail (ToStackStuff binder body'))
toCps (ApplyAction f x) k = do
  toCps f $ \f' -> k (ApplyCps f' (toCpsThing x))
toCps (LetToAction action binder body) k = do
  toCps action $ \act -> do
      body' <- toCps body k
      pure (JumpEffect act (ToStackStuff binder body'))
toCps (LetBeAction value binder body) k = do
      body' <- toCps body k
      pure (JumpEffect (ReturnCps (toCpsThing value)) (ToStackStuff binder body'))
toCps (CatchAction binder body) k = do
  -- fixme...
  label <- getLabel undefined
  body' <- toCps body $ \x -> do
      pure (JumpEffect x (VariableStuff binder))
  k' <- k (LabelCps label)
  pure $ JumpEffect (ReturnCps (LabelStackStuff label k')) $ ToStackStuff binder body'
toCps (ThrowAction val body) _ = do
  toCps body $ \x -> do
      pure (JumpEffect x (toCpsThing val))

toCpsThing :: Thing a -> Stuff a
toCpsThing (ConstantThing x) = ConstantStuff x
toCpsThing (VariableThing x) = VariableStuff x
