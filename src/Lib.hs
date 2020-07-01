{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving, FlexibleContexts #-}
module Lib
    (
      fn, thunk, int, plus,
      Term (..),
      Variable (..),
      Constant (..),
      Global (Global ),
      Type (), Code (), Action (), Stuff (), Stack (), F (), U (), (:->) (),
      CompilerState (..), Compiler,
      inlineTerm, simplifyTerm, toCallByPushValue, toExplicitCatchThrow, toCps',
      intrinsify, simplifyCbpv
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
import Callcc
import Term (Term (..))
import qualified Term
import Cbpv (Code (..), Value (..))
import qualified Cbpv
import Cps

inlineTerm = Term.inline
simplifyTerm = Term.simplify
simplifyCbpv = Cbpv.simplify
intrinsify = Cbpv.intrinsify

thunkify :: Variable a -> Variable (U a)
thunkify (Variable (Type t) name) = let
  Type thunk' = thunk
  in Variable (Type (ApplyName thunk' t)) name

toCallByPushValue :: Term a -> Code a
toCallByPushValue (VariableTerm x) = ForceCode (VariableValue (thunkify x))
toCallByPushValue (ConstantTerm x) = ConstantCode x
toCallByPushValue (GlobalTerm x) = GlobalCode x
toCallByPushValue (LetTerm term binder body) = let
  term' = toCallByPushValue term
  binder' = thunkify binder
  body' = toCallByPushValue body
  in LetBeCode (ThunkValue term') binder' body'
toCallByPushValue (LambdaTerm binder body) = let
  binder' = thunkify binder
  body' = toCallByPushValue body
  in LambdaCode binder' body'
toCallByPushValue (ApplyTerm f x) = ApplyCode (toCallByPushValue f) (ThunkValue (toCallByPushValue x))



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
toExplicitCatchThrow (LetBeCode value binder body) = do
  body' <- toExplicitCatchThrow body
  toExplicitCatchThrowValue value $ \value' -> LetBeAction value' binder body'
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

toCps :: Action a -> (Cps a -> Compiler Effect) -> Compiler Effect
toCps (ConstantAction x) k = k (ConstantCps x)
toCps (GlobalAction x) k = k (GlobalCps x)
toCps (ReturnAction value) k = k (ReturnCps (VariableStuff value))
toCps (LambdaAction binder body) k = do
  tail <- getVariable undefined
  body' <- toCps body $ \b -> do
    pure (JumpEffect b (VariableStuff tail))

  k (LambdaCps tail (ToStackStuff binder body'))
toCps (ApplyAction f x) k = do
  toCps f $ \f' -> k (ApplyCps f' (VariableStuff x))
toCps (LetToAction action binder body) k = do
  toCps action $ \act -> do
      body' <- toCps body k
      pure (JumpEffect act (ToStackStuff binder body'))
toCps (LetBeAction value binder body) k = do
      body' <- toCps body k
      pure (JumpEffect (ReturnCps (VariableStuff value)) (ToStackStuff binder body'))
toCps (CatchAction binder body) k = do
  -- fixme...
  label <- getLabel undefined
  body' <- toCps body $ \x -> do
      pure (JumpEffect x (VariableStuff binder))
  k' <- k (LabelCps label)
  pure $ JumpEffect (ReturnCps (LabelStackStuff label k')) $ ToStackStuff binder body'
toCps (ThrowAction binder body) _ = do
  toCps body $ \x -> do
      pure (JumpEffect x (VariableStuff binder))
