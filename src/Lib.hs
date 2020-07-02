{-# LANGUAGE GADTs, TypeOperators #-}
module Lib
    (
      fn, thunk, int, plus,
      Build (..),
      Term,
      Variable (..),
      Constant (..),
      Global (Global ),
      Type (..), Action (), Stack (), F (), U (), (:->) (),
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
import Term (Build (..), Term (..))
import qualified Term
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

toCallByPushValue :: Term a -> Compiler (Cbpv.Code a)
toCallByPushValue (VariableTerm x) = pure $ Cbpv.ForceCode (Cbpv.VariableValue x)
toCallByPushValue (ConstantTerm x) = pure $ Cbpv.ReturnCode (Cbpv.ConstantValue x)
toCallByPushValue (GlobalTerm x) = pure $ Cbpv.GlobalCode x
toCallByPushValue (LetTerm term binder body) = do
  term' <- toCallByPushValue term
  body' <- toCallByPushValue body
  pure $ Cbpv.LetBeCode (Cbpv.ThunkValue term') binder body'
toCallByPushValue (LambdaTerm binder body) = do
  body' <- toCallByPushValue body
  pure $ Cbpv.LambdaCode binder body'
toCallByPushValue (ApplyTerm f x) = do
  f' <- toCallByPushValue f
  x' <- toCallByPushValue x
  pure $ Cbpv.ApplyCode f' (Cbpv.ThunkValue x')



toExplicitCatchThrow :: Cbpv.Code a -> Compiler (Action a)
toExplicitCatchThrow (Cbpv.GlobalCode x) = pure (GlobalAction x)
toExplicitCatchThrow (Cbpv.LambdaCode binder body) = do
  body' <- toExplicitCatchThrow body
  pure (LambdaAction binder body')
toExplicitCatchThrow (Cbpv.ApplyCode f x) = do
  f' <- toExplicitCatchThrow f
  toExplicitCatchThrowValue x (\x' -> ApplyAction f' x')
toExplicitCatchThrow (Cbpv.LetToCode action binder body) = do
  action' <- toExplicitCatchThrow action
  body' <- toExplicitCatchThrow body
  return (LetToAction action' binder body')
toExplicitCatchThrow (Cbpv.LetBeCode value binder body) = do
  body' <- toExplicitCatchThrow body
  toExplicitCatchThrowValue value $ \value' -> LetBeAction value' binder body'
toExplicitCatchThrow (Cbpv.ReturnCode x) = toExplicitCatchThrowValue x $ \x' -> ReturnAction x'
toExplicitCatchThrow (Cbpv.ForceCode thunk) = do
  -- fixme...
  v <- getVariable undefined
  toExplicitCatchThrowValue thunk $ \thunk' -> CatchAction v (ThrowAction thunk' (ReturnAction (VariableThing v)))

toExplicitCatchThrowValue :: Cbpv.Value a -> (Thing a -> Action b) -> Compiler (Action b)
toExplicitCatchThrowValue (Cbpv.ConstantValue x) k = pure (k (ConstantThing x))
toExplicitCatchThrowValue (Cbpv.VariableValue v) k = pure (k (VariableThing v))
toExplicitCatchThrowValue (Cbpv.ThunkValue code) k = do
  -- fixme...
  returner <- getVariable undefined
  label <- getVariable undefined
  binder <- getVariable undefined
  code' <- toExplicitCatchThrow code
  pure $ CatchAction returner $ LetToAction
      (CatchAction label (ThrowAction (VariableThing returner) (k (VariableThing label))))
      binder
      (ThrowAction (VariableThing binder) code')



toCps' :: Action a -> Compiler (Cps.Code a)
toCps' act = do
  k <- getVariable undefined
  eff <- toCps act $ \a -> Cps.JumpEffect a (Cps.VariableValue k)
  pure (Cps.KontCode k eff)

toCps :: Action a -> (Cps.Code a -> Effect) -> Compiler Effect
toCps (GlobalAction x) k = pure $ k $ Cps.GlobalCode x
toCps (ReturnAction value) k = pure $ k $ Cps.ReturnCode (toCpsThing value)
toCps (LambdaAction binder body) k = do
  tail <- getVariable undefined
  body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableValue tail)
  pure $ k $ Cps.LambdaCode binder (Cps.KontCode tail body')
toCps (ApplyAction f x) k = do
  toCps f $ \f' -> k $ Cps.ApplyCode f' (toCpsThing x)
toCps (LetToAction action binder body) k = do
  s <- getVariable undefined
  b <- toCps body $ \bod -> Cps.JumpEffect bod (Cps.VariableValue s)
  toCps action $ \act -> k $ Cps.LetToCode act binder (Cps.KontCode s b)

toCps (LetBeAction value binder body) k = do
    t <- getVariable undefined
    body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableValue t)
    pure $ k $ Cps.LetBeCode (toCpsThing value) binder (Cps.KontCode t body')
toCps (CatchAction binder body) k = do
  body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableValue binder)
  pure $ k $ Cps.KontCode binder body'
toCps (ThrowAction val body) _ = do
  toCps body $ \body' -> Cps.JumpEffect body' (toCpsThing val)

toCpsThing :: Thing a -> Cps.Value a
toCpsThing (ConstantThing x) = Cps.ConstantValue x
toCpsThing (VariableThing x) = Cps.VariableValue x
