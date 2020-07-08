{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Lib
  ( toCallByPushValue,
    toCallcc,
    toContinuationPassingStyle,
  )
where

import qualified Callcc
import qualified Cbpv
import Common
import Core
import qualified Cps
import qualified Data.Text as T
import qualified SystemF
import TextShow
import Type
import Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

toCallByPushValue :: Cbpv.Cbpv t => SystemF.Term a -> t Cbpv.Code a
toCallByPushValue = toCbpv VarMap.empty

toCbpv :: Cbpv.Cbpv t => VarMap (t Cbpv.Code) -> SystemF.Term a -> t Cbpv.Code a
toCbpv env (SystemF.VariableTerm x) =
  let Just replacement = VarMap.lookup x env
   in replacement
toCbpv _ (SystemF.ConstantTerm x) = Cbpv.returns (Cbpv.constant x)
toCbpv _ (SystemF.GlobalTerm x) = Cbpv.global x
toCbpv env (SystemF.LetTerm term binder body) =
  let term' = toCbpv env term
   in Cbpv.letBe (Cbpv.delay term') $ \value ->
        let env' = VarMap.insert binder (Cbpv.force value) env
         in toCbpv env' body
toCbpv env (SystemF.LambdaTerm binder@(Variable t _) body) =
  Cbpv.lambda (U t) $ \value ->
    let env' = VarMap.insert binder (Cbpv.force value) env
     in toCbpv env' body
toCbpv env (SystemF.ApplyTerm f x) =
  let f' = toCbpv env f
      x' = toCbpv env x
   in Cbpv.apply f' (Cbpv.delay x')

toCallcc :: Cbpv.Code a -> Callcc.Code a
toCallcc x = Callcc.build $ toExplicitCatchThrow VarMap.empty x

toExplicitCatchThrow :: Callcc.Callcc t => VarMap (t Callcc.Data) -> Cbpv.Code a -> t Callcc.Code a
toExplicitCatchThrow _ (Cbpv.GlobalCode x) = Callcc.global x
toExplicitCatchThrow env (Cbpv.LambdaCode binder@(Variable t _) body) =
  Callcc.lambda t $ \x ->
    toExplicitCatchThrow (VarMap.insert binder x env) body
toExplicitCatchThrow env ap@(Cbpv.ApplyCode f x) =
  let f' = toExplicitCatchThrow env f
      x' = toExplicitCatchThrowData env x
   in Callcc.letTo x' $ \val ->
        Callcc.apply f' val
toExplicitCatchThrow env (Cbpv.LetToCode action binder body) =
  let action' = toExplicitCatchThrow env action
   in Callcc.letTo action' $ \x ->
        toExplicitCatchThrow (VarMap.insert binder x env) body
toExplicitCatchThrow env (Cbpv.LetBeCode value binder body) =
  let value' = toExplicitCatchThrowData env value
   in Callcc.letTo value' $ \x ->
        toExplicitCatchThrow (VarMap.insert binder x env) body
toExplicitCatchThrow env (Cbpv.ReturnCode x) =
  toExplicitCatchThrowData env x
toExplicitCatchThrow env f@(Cbpv.ForceCode thunk) =
  let t = Cbpv.typeOf f
      thunk' = toExplicitCatchThrowData env thunk
   in Callcc.letTo thunk' $ \val ->
        Callcc.catch t $ \v ->
          Callcc.throw val (Callcc.returns v)

toExplicitCatchThrowData :: Callcc.Callcc t => VarMap (t Callcc.Data) -> Cbpv.Data a -> t Callcc.Code (F a)
toExplicitCatchThrowData _ (Cbpv.ConstantData x) = Callcc.returns (Callcc.constant x)
toExplicitCatchThrowData env (Cbpv.VariableData v) =
  let Just x = VarMap.lookup v env
   in Callcc.returns x
toExplicitCatchThrowData env (Cbpv.ThunkData code) =
  let code' = toExplicitCatchThrow env code
      t = Cbpv.typeOf code
   in Callcc.catch (F (StackType (F (StackType t)))) $ \returner ->
        Callcc.letTo
          ( Callcc.catch (F (StackType t)) $ \label ->
              Callcc.throw returner (Callcc.returns label)
          )
          $ \binder ->
            (Callcc.throw binder code')

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code a -> t Cps.Data (Stack (F (Stack a)))
toContinuationPassingStyle = toCps' VarMap.empty

toCps' :: Cps.Cps t => VarMap (t Cps.Data) -> Callcc.Code a -> t Cps.Data (Stack (F (Stack a)))
toCps' env act =
  let t = Callcc.typeOf act
   in Cps.letTo (StackType t) $ \k ->
        toCps env act k

toCps :: Cps.Cps t => VarMap (t Cps.Data) -> Callcc.Code a -> t Cps.Data (Stack a) -> t Cps.Code Nil
toCps env (Callcc.ApplyCode f x) k =
  toCps env f (Cps.push (toCpsData env x) k)
toCps env (Callcc.LetBeCode value binder body) k =
  Cps.letBe (toCpsData env value) $ \value ->
    let env' = VarMap.insert binder value env
     in toCps env' body k
toCps env (Callcc.ThrowCode val body) _ =
  toCps env body (toCpsData env val)
toCps env (Callcc.LetToCode action binder@(Variable t _) body) k =
  let F t = Callcc.typeOf action
   in toCps env action $ Cps.letTo t $ \value ->
        let env' = VarMap.insert binder value env
         in toCps env' body k
toCps env (Callcc.CatchCode binder@(Variable t _) body) k =
  Cps.letBe k $ \k' ->
    let env' = VarMap.insert binder k' env
     in toCps env' body Cps.nilStack
toCps _ (Callcc.GlobalCode x) k = Cps.jump (Cps.global x) k
toCps env (Callcc.ReturnCode value) k = Cps.jump (Cps.returns (toCpsData env value)) k

toCpsData :: Cps.Cps t => VarMap (t Cps.Data) -> Callcc.Data a -> t Cps.Data a
toCpsData _ (Callcc.ConstantData x) = Cps.constant x
toCpsData env (Callcc.VariableData v) =
  let Just x = VarMap.lookup v env
   in x
