{-# LANGUAGE GADTs, TypeOperators #-}
module Lib
    (
      fn, thunk, int, plus,
      Build (..),
      Term,
      Variable (..),
      Constant (..),
      Global (Global ),
      Type (..), Stack (), F (), U (), (:->) (),
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
import Term (Build (..), Term (..))
import qualified Term
import qualified Cbpv
import qualified Callcc
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



toExplicitCatchThrow :: Cbpv.Code a -> Compiler (Callcc.Code a)
toExplicitCatchThrow (Cbpv.GlobalCode x) = pure (Callcc.GlobalCode x)
toExplicitCatchThrow (Cbpv.LambdaCode binder body) = do
  body' <- toExplicitCatchThrow body
  pure (Callcc.LambdaCode binder body')
toExplicitCatchThrow (Cbpv.ApplyCode f x) = do
  f' <- toExplicitCatchThrow f
  toExplicitCatchThrowValue x (\x' -> Callcc.ApplyCode f' x')
toExplicitCatchThrow (Cbpv.LetToCode action binder body) = do
  action' <- toExplicitCatchThrow action
  body' <- toExplicitCatchThrow body
  return (Callcc.LetToCode action' binder body')
toExplicitCatchThrow (Cbpv.LetBeCode value binder body) = do
  body' <- toExplicitCatchThrow body
  toExplicitCatchThrowValue value $ \value' -> Callcc.LetBeCode value' binder body'
toExplicitCatchThrow (Cbpv.ReturnCode x) = toExplicitCatchThrowValue x $ \x' -> Callcc.ReturnCode x'
toExplicitCatchThrow (Cbpv.ForceCode thunk) = do
  -- fixme...
  v <- getVariable undefined
  toExplicitCatchThrowValue thunk $ \thunk' -> Callcc.CatchCode v (Callcc.ThrowCode thunk' (Callcc.ReturnCode (Callcc.VariableValue v)))

toExplicitCatchThrowValue :: Cbpv.Value a -> (Callcc.Value a -> Callcc.Code b) -> Compiler (Callcc.Code b)
toExplicitCatchThrowValue (Cbpv.ConstantValue x) k = pure (k (Callcc.ConstantValue x))
toExplicitCatchThrowValue (Cbpv.VariableValue v) k = pure (k (Callcc.VariableValue v))
toExplicitCatchThrowValue (Cbpv.ThunkValue code) k = do
  -- fixme...
  returner <- getVariable undefined
  label <- getVariable undefined
  binder <- getVariable undefined
  code' <- toExplicitCatchThrow code
  pure $ Callcc.CatchCode returner $ Callcc.LetToCode
      (Callcc.CatchCode label (Callcc.ThrowCode (Callcc.VariableValue returner) (k (Callcc.VariableValue label))))
      binder
      (Callcc.ThrowCode (Callcc.VariableValue binder) code')



toCps' :: Callcc.Code a -> Compiler (Cps.Code a)
toCps' act = do
  k <- getVariable undefined
  eff <- toCps act $ \a -> Cps.JumpEffect a (Cps.VariableValue k)
  pure (Cps.KontCode k eff)

toCps :: Callcc.Code a -> (Cps.Code a -> Effect) -> Compiler Effect
toCps (Callcc.GlobalCode x) k = pure $ k $ Cps.GlobalCode x
toCps (Callcc.ReturnCode value) k = pure $ k $ Cps.ReturnCode (toCpsValue value)
toCps (Callcc.LambdaCode binder body) k = do
  tail <- getVariable undefined
  body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableValue tail)
  pure $ k $ Cps.LambdaCode binder (Cps.KontCode tail body')
toCps (Callcc.ApplyCode f x) k = do
  toCps f $ \f' -> k $ Cps.ApplyCode f' (toCpsValue x)
toCps (Callcc.LetToCode action binder body) k = do
  s <- getVariable undefined
  b <- toCps body $ \bod -> Cps.JumpEffect bod (Cps.VariableValue s)
  toCps action $ \act -> k $ Cps.LetToCode act binder (Cps.KontCode s b)

toCps (Callcc.LetBeCode value binder body) k = do
    t <- getVariable undefined
    body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableValue t)
    pure $ k $ Cps.LetBeCode (toCpsValue value) binder (Cps.KontCode t body')
toCps (Callcc.CatchCode binder body) k = do
  body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableValue binder)
  pure $ k $ Cps.KontCode binder body'
toCps (Callcc.ThrowCode val body) _ = do
  toCps body $ \body' -> Cps.JumpEffect body' (toCpsValue val)

toCpsValue :: Callcc.Value a -> Cps.Value a
toCpsValue (Callcc.ConstantValue x) = Cps.ConstantValue x
toCpsValue (Callcc.VariableValue x) = Cps.VariableValue x
