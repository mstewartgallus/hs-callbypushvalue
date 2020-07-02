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
      inlineTerm, simplifyTerm, toCallByPushValue, toCallcc, toCps',
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
import qualified VarMap
import VarMap (VarMap)
import Unique

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

toCallByPushValue :: Term a -> Cbpv.Code a
toCallByPushValue (VariableTerm x) = Cbpv.ForceCode (Cbpv.VariableData x)
toCallByPushValue (ConstantTerm x) = Cbpv.ReturnCode (Cbpv.ConstantData x)
toCallByPushValue (GlobalTerm x) = Cbpv.GlobalCode x
toCallByPushValue (LetTerm term binder body) = let
  term' = toCallByPushValue term
  body' = toCallByPushValue body
  in Cbpv.LetBeCode (Cbpv.ThunkData term') binder body'
toCallByPushValue (LambdaTerm binder body) = let
  body' = toCallByPushValue body
  in Cbpv.LambdaCode binder body'
toCallByPushValue (ApplyTerm f x) = let
  f' = toCallByPushValue f
  x' = toCallByPushValue x
  in Cbpv.ApplyCode f' (Cbpv.ThunkData x')



toCallcc :: Cbpv.Code a -> Unique.Stream -> Callcc.Code a
toCallcc x = Callcc.build $ toExplicitCatchThrow VarMap.empty x

data X a = X (Callcc.DataBuilder a)

toExplicitCatchThrow :: VarMap X -> Cbpv.Code a -> Callcc.CodeBuilder a
toExplicitCatchThrow _ (Cbpv.GlobalCode x) = Callcc.GlobalBuilder x
toExplicitCatchThrow env (Cbpv.LambdaCode binder@(Variable t _) body) =
  Callcc.LambdaBuilder t $ \x -> toExplicitCatchThrow (VarMap.insert binder (X x) env) body
toExplicitCatchThrow env (Cbpv.ApplyCode f x) = let
  f' = toExplicitCatchThrow env f
  in toExplicitCatchThrowData env x (\x' -> Callcc.ApplyBuilder f' x')
toExplicitCatchThrow env (Cbpv.LetToCode action binder@(Variable t _) body) = let
  action' = toExplicitCatchThrow env action
  in Callcc.LetToBuilder action' t (\x -> toExplicitCatchThrow (VarMap.insert binder (X x) env) body)
toExplicitCatchThrow env (Cbpv.LetBeCode value binder@(Variable t _) body) =
  toExplicitCatchThrowData env value $ \value' -> Callcc.LetBeBuilder value' t (\x ->  toExplicitCatchThrow (VarMap.insert binder (X x) env) body)
toExplicitCatchThrow env (Cbpv.ReturnCode x) = toExplicitCatchThrowData env x $ \x' -> Callcc.ReturnBuilder x'
toExplicitCatchThrow env (Cbpv.ForceCode thunk) =
  -- fixme... get type
  toExplicitCatchThrowData env thunk $ \thunk' -> Callcc.CatchBuilder undefined $ \v -> Callcc.ThrowBuilder thunk' (Callcc.ReturnBuilder v)

toExplicitCatchThrowData :: VarMap X -> Cbpv.Data a -> (Callcc.DataBuilder a -> Callcc.CodeBuilder b) -> Callcc.CodeBuilder b
toExplicitCatchThrowData _ (Cbpv.ConstantData x) k = k (Callcc.ConstantBuilder x)
toExplicitCatchThrowData env (Cbpv.VariableData v) k = let
  Just (X x) = VarMap.lookup v env
  in k x
toExplicitCatchThrowData env (Cbpv.ThunkData code) k = let
  code' = toExplicitCatchThrow env code
  -- fixme...
  in Callcc.CatchBuilder undefined $ \returner ->
  -- fixme...
  Callcc.LetToBuilder (Callcc.CatchBuilder undefined $ \label ->
                          Callcc.ThrowBuilder returner (k label))
    -- fixme...
      undefined
      $ \binder -> (Callcc.ThrowBuilder binder code')



toCps' :: Callcc.Code a -> Compiler (Cps.Code a)
toCps' act = do
  k <- getVariable undefined
  eff <- toCps act $ \a -> Cps.JumpEffect a (Cps.VariableData k)
  pure (Cps.KontCode k eff)

toCps :: Callcc.Code a -> (Cps.Code a -> Effect) -> Compiler Effect
toCps (Callcc.GlobalCode x) k = pure $ k $ Cps.GlobalCode x
toCps (Callcc.ReturnCode value) k = pure $ k $ Cps.ReturnCode (toCpsData value)
toCps (Callcc.LambdaCode binder body) k = do
  tail <- getVariable undefined
  body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableData tail)
  pure $ k $ Cps.LambdaCode binder (Cps.KontCode tail body')
toCps (Callcc.ApplyCode f x) k = do
  toCps f $ \f' -> k $ Cps.ApplyCode f' (toCpsData x)
toCps (Callcc.LetToCode action binder body) k = do
  b <- toCps body k
  toCps action $ \act -> Cps.JumpEffect act $ Cps.LetToStackData binder b

toCps (Callcc.LetBeCode value binder body) k = do
    t <- getVariable undefined
    body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableData t)
    pure $ k $ Cps.LetBeCode (toCpsData value) binder (Cps.KontCode t body')
toCps (Callcc.CatchCode binder body) k = do
  body' <- toCps body $ \b -> Cps.JumpEffect b (Cps.VariableData binder)
  pure $ k $ Cps.KontCode binder body'
toCps (Callcc.ThrowCode val body) _ = do
  toCps body $ \body' -> Cps.JumpEffect body' (toCpsData val)

toCpsData :: Callcc.Data a -> Cps.Data a
toCpsData (Callcc.ConstantData x) = Cps.ConstantData x
toCpsData (Callcc.VariableData x) = Cps.VariableData x
