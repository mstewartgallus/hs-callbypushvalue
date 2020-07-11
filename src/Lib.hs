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
import Label
import qualified LabelMap
import LabelMap (LabelMap)
import qualified SystemF
import Type
import qualified VarMap
import VarMap (VarMap)
import Variable

toCallByPushValue :: Cbpv.Cbpv t => SystemF.Term a -> t Cbpv.Code a
toCallByPushValue = toCbpv LabelMap.empty

toCbpv :: Cbpv.Cbpv t => LabelMap (t Cbpv.Code) -> SystemF.Term a -> t Cbpv.Code a
toCbpv env (SystemF.LabelTerm x) =
  let Just x' = LabelMap.lookup x env
   in x'
toCbpv _ (SystemF.ConstantTerm x) = Cbpv.returns (Cbpv.constant x)
toCbpv _ (SystemF.GlobalTerm x) = Cbpv.global x
toCbpv env (SystemF.LetTerm term binder body) =
  let term' = toCbpv env term
   in Cbpv.letBe (Cbpv.delay term') $ \value ->
        let env' = LabelMap.insert binder (Cbpv.force value) env
         in toCbpv env' body
toCbpv env (SystemF.LambdaTerm binder@(Label t _) body) =
  Cbpv.lambda (U t) $ \value ->
    let env' = LabelMap.insert binder (Cbpv.force value) env
     in toCbpv env' body
toCbpv env (SystemF.ApplyTerm f x) =
  let f' = toCbpv env f
      x' = toCbpv env x
   in Cbpv.apply f' (Cbpv.delay x')

toCallcc :: Cbpv.Code a -> Callcc.Code a
toCallcc x = Callcc.build (callcc VarMap.empty x)

callcc :: Callcc.Callcc t => VarMap (t Callcc.Data) -> Cbpv.Code a -> t Callcc.Code a
callcc env (Cbpv.LambdaCode binder@(Variable t _) body) =
  Callcc.lambda t $ \x ->
    callcc (VarMap.insert binder x env) body
callcc env (Cbpv.ApplyCode f x) =
  let x' = callccData env x
      f' = callcc env f
   in Callcc.apply f' x'
callcc env (Cbpv.LetToCode action binder body) =
  Callcc.letTo (callcc env action) $ \x ->
    callcc (VarMap.insert binder x env) body
callcc env (Cbpv.LetBeCode value binder body) =
  Callcc.letBe (callccData env value) $ \x ->
    callcc (VarMap.insert binder x env) body
callcc env (Cbpv.ReturnCode x) = Callcc.returns (callccData env x)
callcc env x@(Cbpv.ForceCode thunk) =
  let t = Cbpv.typeOf x
      thunk' = callccData env thunk
   in Callcc.catch t $ \x ->
        Callcc.force thunk' x
callcc _ (Cbpv.GlobalCode x) = Callcc.global x

callccData :: Callcc.Callcc t => VarMap (t Callcc.Data) -> Cbpv.Data a -> t Callcc.Data a
callccData _ (Cbpv.ConstantData x) = Callcc.constant x
callccData env (Cbpv.VariableData v) =
  let Just x = VarMap.lookup v env
   in x
callccData env (Cbpv.ThunkData code) =
  let t = Cbpv.typeOf code
      c = callcc env code
   in Callcc.thunk t $ \x ->
        Callcc.throw x c

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code a -> t (Cps.Data (U a))
toContinuationPassingStyle = toCpsThunk LabelMap.empty VarMap.empty

toCpsThunk :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (Cps.Data (U a))
toCpsThunk lenv env act =
  let t = Callcc.typeOf act
   in Cps.thunk t $ \k -> toCps lenv env act k

toCps :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (Cps.Stack a) -> t Cps.Code
toCps lenv env (Callcc.ApplyCode f x) k =
  let x' = toCpsData lenv env x
   in toCps lenv env f (Cps.push x' k)
toCps lenv env (Callcc.LetBeCode value binder body) k =
  Cps.letBe (toCpsData lenv env value) $ \val ->
    let env' = VarMap.insert binder (Y val) env
     in toCps lenv env' body k
toCps lenv env (Callcc.LambdaCode binder@(Variable t _) body) k =
  Cps.pop k $ \x ->
    let env' = VarMap.insert binder (Y x) env
     in toCpsThunk lenv env' body
toCps lenv env (Callcc.LetToCode action binder@(Variable t _) body) k =
  toCps lenv env action $ Cps.letTo t $ \y ->
    let env' = VarMap.insert binder (Y y) env
     in toCps lenv env' body k
toCps lenv env (Callcc.CatchCode binder@(Label t _) body) k =
  Cps.label k $ \k' ->
    let lenv' = LabelMap.insert binder (L k') lenv
     in toCps lenv' env body Cps.nilStack
toCps _ _ (Callcc.GlobalCode x) k = Cps.global x k
toCps lenv env (Callcc.ForceCode thunk stack) _ =
  Cps.force (toCpsData lenv env thunk) (toCpsStack lenv env stack)
toCps lenv env (Callcc.ThrowCode k body) _ =
  toCps lenv env body (toCpsStack lenv env k)

newtype L t a = L (t (Cps.Stack a))

newtype Y t a = Y (t (Cps.Data a))

toCpsStack :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Stack a -> t (Cps.Stack a)
toCpsStack lenv _ (Callcc.LabelData v) =
  let Just (L x) = LabelMap.lookup v lenv
   in x

toCpsData :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Data a -> t (Cps.Data a)
toCpsData _ _ (Callcc.ConstantData x) = Cps.constant x
toCpsData _ env (Callcc.VariableData v) =
  let Just (Y x) = VarMap.lookup v env
   in x
toCpsData lenv env (Callcc.ThunkData label@(Label t _) body) =
  Cps.thunk t $ \k ->
    let lenv' = LabelMap.insert label (L k) lenv
     in toCps lenv' env body Cps.nilStack
