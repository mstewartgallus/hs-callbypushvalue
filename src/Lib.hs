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

toCallByPushValue :: SystemF.Term a -> Cbpv.Builder Cbpv.Code a
toCallByPushValue = toCbpv VarMap.empty

newtype C a = C (Cbpv.Builder Cbpv.Code a)

toCbpv :: VarMap C -> SystemF.Term a -> Cbpv.Builder Cbpv.Code a
toCbpv env (VariableTerm x) =
  let Just (C replacement) = VarMap.lookup x env
   in replacement
toCbpv _ (ConstantTerm x) = Cbpv.returns (Cbpv.constant x)
toCbpv _ (GlobalTerm x) = Cbpv.global x
toCbpv env (LetTerm term binder body) =
  let term' = toCbpv env term
   in Cbpv.letBe (Cbpv.delay term') $ \value ->
        let env' = VarMap.insert binder (C (Cbpv.force value)) env
         in toCbpv env' body
toCbpv env (LambdaTerm binder@(Variable t _) body) =
  Cbpv.lambda (applyType thunk t) $ \value ->
    let env' = VarMap.insert binder (C (Cbpv.force value)) env
     in toCbpv env' body
toCbpv env (ApplyTerm f x) =
  let f' = toCbpv env f
      x' = toCbpv env x
   in Cbpv.apply f' (Cbpv.delay x')

toCallcc :: Cbpv.Code a -> Callcc.Code a
toCallcc x = Callcc.build $ toExplicitCatchThrow VarMap.empty x

data X a = X (Callcc.Builder Callcc.Data a)

toExplicitCatchThrow :: VarMap X -> Cbpv.Code a -> Callcc.Builder Callcc.Code a
toExplicitCatchThrow _ (Cbpv.GlobalCode x) = Callcc.global x
toExplicitCatchThrow env (Cbpv.LambdaCode binder@(Variable t _) body) =
  Callcc.lambda t $ \x -> toExplicitCatchThrow (VarMap.insert binder (X x) env) body
toExplicitCatchThrow env ap@(Cbpv.ApplyCode f x) =
  let f' = toExplicitCatchThrow env f
      x' = toExplicitCatchThrowData env x
   in Callcc.letTo x' $ \val ->
        Callcc.apply f' val
toExplicitCatchThrow env (Cbpv.LetToCode action binder body) =
  let action' = toExplicitCatchThrow env action
   in Callcc.letTo action' $ \x ->
        toExplicitCatchThrow (VarMap.insert binder (X x) env) body
toExplicitCatchThrow env (Cbpv.LetBeCode value binder body) =
  let value' = toExplicitCatchThrowData env value
   in Callcc.letTo value' $ \x ->
        toExplicitCatchThrow (VarMap.insert binder (X x) env) body
toExplicitCatchThrow env (Cbpv.ReturnCode x) =
  toExplicitCatchThrowData env x
toExplicitCatchThrow env f@(Cbpv.ForceCode thunk) =
  let t = Cbpv.typeOf f
      thunk' = toExplicitCatchThrowData env thunk
   in Callcc.letTo thunk' $ \val ->
        Callcc.catch t $ \v ->
          Callcc.throw val (Callcc.returns v)

toExplicitCatchThrowData :: VarMap X -> Cbpv.Data a -> Callcc.Builder Callcc.Code (F a)
toExplicitCatchThrowData _ (Cbpv.ConstantData x) = Callcc.returns (Callcc.constant x)
toExplicitCatchThrowData env (Cbpv.VariableData v) =
  let Just (X x) = VarMap.lookup v env
   in Callcc.returns x
toExplicitCatchThrowData env (Cbpv.ThunkData code) =
  let code' = toExplicitCatchThrow env code
      t = Cbpv.typeOf code
   in Callcc.catch (applyType returnsType (applyType stack (applyType returnsType (applyType stack t)))) $ \returner ->
        Callcc.letTo
          ( Callcc.catch (applyType returnsType (applyType stack t)) $ \label ->
              Callcc.throw returner (Callcc.returns label)
          )
          $ \binder ->
            (Callcc.throw binder code')

toContinuationPassingStyle :: Callcc.Code a -> Cps.Builder Cps.Data (Stack (F (Stack a)))
toContinuationPassingStyle = toCps' VarMap.empty

toCps' :: VarMap Y -> Callcc.Code a -> Cps.Builder Cps.Data (Stack (F (Stack a)))
toCps' env act =
  let t = Callcc.typeOf act
   in Cps.letTo (applyType stack t) $ \k ->
        toCps env act k

toCps :: VarMap Y -> Callcc.Code a -> Cps.Builder Cps.Data (Stack a) -> Cps.Builder Cps.Code Nil
toCps env (Callcc.ApplyCode f x) k =
  toCps env f (Cps.push (toCpsData env x) k)
toCps env (Callcc.LetBeCode value binder body) k =
  Cps.letBe (toCpsData env value) $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCps env' body k
toCps env (Callcc.ThrowCode val body) _ =
  toCps env body (toCpsData env val)
toCps env (Callcc.LetToCode action binder@(Variable t _) body) k =
  let ReturnsType t = Callcc.typeOf action
   in toCps env action $ Cps.letTo t $ \value ->
        let env' = VarMap.insert binder (Y value) env
         in toCps env' body k
toCps env (Callcc.CatchCode binder@(Variable t _) body) k =
  Cps.letBe k $ \k' ->
    let env' = VarMap.insert binder (Y k') env
     in toCps env' body Cps.nilStack
toCps _ (Callcc.GlobalCode x) k = Cps.jump (Cps.global x) k
toCps env (Callcc.ReturnCode value) k = Cps.jump (Cps.returns (toCpsData env value)) k

newtype Y a = Y (Cps.Builder Cps.Data a)

toCpsData :: VarMap Y -> Callcc.Data a -> Cps.Builder Data a
toCpsData _ (Callcc.ConstantData x) = Cps.constant x
toCpsData env (Callcc.VariableData v) =
  let Just (Y x) = VarMap.lookup v env
   in x
