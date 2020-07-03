{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Lib
  ( fn,
    thunk,
    int,
    plus,
    Variable (..),
    Constant (..),
    Global (Global),
    Type (..),
    Stack (),
    F (),
    U (),
    (:->) (),
    inlineTerm,
    simplifyTerm,
    toCallByPushValue,
    toCallcc,
    toContinuationPassingStyle,
    intrinsify,
    simplifyCbpv,
    inlineCbpv,
    simplifyCallcc,
  )
where

import qualified Callcc
import qualified Cbpv
import Common
import Control.Monad.ST
import Control.Monad.State
import Core
import Cps
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Typeable
import SystemF (Term (..))
import qualified SystemF
import TextShow
import Unique
import qualified VarMap
import VarMap (VarMap)

inlineTerm = SystemF.inline

simplifyTerm = SystemF.simplify

simplifyCbpv = Cbpv.simplify

inlineCbpv = Cbpv.inline

simplifyCallcc = Callcc.simplify

intrinsify = Cbpv.intrinsify

toCallByPushValue :: SystemF.Term a -> Cbpv.Code a
toCallByPushValue (VariableTerm x) = Cbpv.ForceCode (Cbpv.VariableData x)
toCallByPushValue (ConstantTerm x) = Cbpv.ReturnCode (Cbpv.ConstantData x)
toCallByPushValue (GlobalTerm x) = Cbpv.GlobalCode x
toCallByPushValue (LetTerm term binder body) =
  let term' = toCallByPushValue term
      body' = toCallByPushValue body
   in Cbpv.LetBeCode (Cbpv.ThunkData term') binder body'
toCallByPushValue (LambdaTerm binder body) =
  let body' = toCallByPushValue body
   in Cbpv.LambdaCode binder body'
toCallByPushValue (ApplyTerm f x) =
  let f' = toCallByPushValue f
      x' = toCallByPushValue x
   in Cbpv.ApplyCode f' (Cbpv.ThunkData x')

toCallcc :: Cbpv.Code a -> Unique.Stream -> Callcc.Code a
toCallcc x = Callcc.build $ toExplicitCatchThrow VarMap.empty x

data X a = X (Callcc.DataBuilder a)

toExplicitCatchThrow :: VarMap X -> Cbpv.Code a -> Callcc.CodeBuilder a
toExplicitCatchThrow _ (Cbpv.GlobalCode x) = Callcc.GlobalBuilder x
toExplicitCatchThrow env (Cbpv.LambdaCode binder@(Variable t _) body) =
  Callcc.LambdaBuilder t $ \x -> toExplicitCatchThrow (VarMap.insert binder (X x) env) body
toExplicitCatchThrow env ap@(Cbpv.ApplyCode f x) =
  let f' = toExplicitCatchThrow env f
   in toExplicitCatchThrowData env x (Cbpv.typeOf ap) (\x' -> Callcc.ApplyBuilder f' x')
toExplicitCatchThrow env (Cbpv.LetToCode action binder@(Variable t _) body) =
  let action' = toExplicitCatchThrow env action
   in Callcc.LetToBuilder action' t (\x -> toExplicitCatchThrow (VarMap.insert binder (X x) env) body)
toExplicitCatchThrow env (Cbpv.LetBeCode value binder@(Variable t _) body) =
  toExplicitCatchThrowData env value (Cbpv.typeOf body) $ \value' -> Callcc.LetBeBuilder value' t (\x -> toExplicitCatchThrow (VarMap.insert binder (X x) env) body)
toExplicitCatchThrow env (Cbpv.ReturnCode x) = toExplicitCatchThrowData env x undefined Callcc.ReturnBuilder
toExplicitCatchThrow env f@(Cbpv.ForceCode thunk) =
  let t = Cbpv.typeOf f
   in -- fixme... get type
      toExplicitCatchThrowData env thunk t $ \thunk' ->
        Callcc.CatchBuilder t $ \v ->
          Callcc.ThrowBuilder thunk' (Callcc.ReturnBuilder v)

toExplicitCatchThrowData :: VarMap X -> Cbpv.Data a -> Type b -> (Callcc.DataBuilder a -> Callcc.CodeBuilder b) -> Callcc.CodeBuilder b
toExplicitCatchThrowData _ (Cbpv.ConstantData x) _ k = k (Callcc.ConstantBuilder x)
toExplicitCatchThrowData env (Cbpv.VariableData v) _ k =
  let Just (X x) = VarMap.lookup v env
   in k x
toExplicitCatchThrowData env (Cbpv.ThunkData code) kt k =
  let code' = toExplicitCatchThrow env code
      t = Cbpv.typeOf code
   in -- fixme...
      Callcc.CatchBuilder kt $ \returner ->
        Callcc.LetToBuilder
          ( Callcc.CatchBuilder (ApplyType returnsType (ApplyType stack t)) $ \label ->
              Callcc.ThrowBuilder returner (k label)
          )
          (ApplyType stack t)
          $ \binder ->
            (Callcc.ThrowBuilder binder code')

toContinuationPassingStyle :: Callcc.Code a -> Cps.CodeBuilder a
toContinuationPassingStyle = toCps' VarMap.empty

toCps' :: VarMap Y -> Callcc.Code a -> Cps.CodeBuilder a
toCps' _ (Callcc.GlobalCode x) = Cps.GlobalBuilder x
toCps' env (Callcc.ReturnCode value) = Cps.ReturnBuilder (toCpsData env value)
toCps' env (Callcc.LambdaCode binder@(Variable t _) body) =
  Cps.LambdaBuilder t $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCps' env' body
toCps' env (Callcc.ApplyCode f x) =
  let f' = toCps' env f
   in Cps.ApplyBuilder f' (toCpsData env x)
toCps' env act =
  let x = Callcc.typeOf act
   in Cps.KontBuilder x $ \k ->
        toCps env act $ \a ->
          Cps.JumpBuilder a k

toCps :: VarMap Y -> Callcc.Code a -> (Cps.CodeBuilder a -> Cps.CodeBuilder R) -> Cps.CodeBuilder R
toCps env (Callcc.ApplyCode f x) k =
  toCps env f $ \f' ->
    k $ Cps.ApplyBuilder f' (toCpsData env x)
toCps env (Callcc.LetBeCode value binder@(Variable t _) body) k =
  k $ Cps.LetBeBuilder (toCpsData env value) $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCps' env' body
toCps env (Callcc.ThrowCode val body) _ = do
  toCps env body $ \body' ->
    Cps.JumpBuilder body' (toCpsData env val)
toCps env (Callcc.LetToCode action binder@(Variable t _) body) k =
  toCps env action $ \act ->
    Cps.JumpBuilder act $ Cps.LetToStackBuilder t $ \value ->
      let env' = VarMap.insert binder (Y value) env
       in toCps env' body k
toCps env (Callcc.CatchCode binder@(Variable (StackType t) _) body) k =
  k $ Cps.KontBuilder t $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCps env' body id
toCps env act k =
  let val = toCps' env act
   in k $ val

newtype Y a = Y (DataBuilder a)

toCpsData :: VarMap Y -> Callcc.Data a -> Cps.DataBuilder a
toCpsData _ (Callcc.ConstantData x) = Cps.ConstantBuilder x
toCpsData env (Callcc.VariableData v) =
  let Just (Y x) = VarMap.lookup v env
   in x
