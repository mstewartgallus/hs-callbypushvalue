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
toCbpv _ (SystemF.GlobalTerm x) = Cbpv.force (Cbpv.global x)
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

callccData :: Callcc.Callcc t => VarMap (t Callcc.Data) -> Cbpv.Data a -> t Callcc.Data a
callccData _ (Cbpv.GlobalData x) = Callcc.global x
callccData _ (Cbpv.ConstantData x) = Callcc.constant x
callccData env (Cbpv.VariableData v) =
  let Just x = VarMap.lookup v env
   in x
callccData env (Cbpv.ThunkData code) =
  let t = Cbpv.typeOf code
      c = callcc env code
   in Callcc.thunk t $ \x ->
        Callcc.throw x c

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code a -> t (U a)
toContinuationPassingStyle = toCps' LabelMap.empty VarMap.empty

toCps' :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (U a)
toCps' lenv env act =
  let t = Callcc.typeOf act
   in Cps.thunk t $ \k -> toCps lenv env act k

toCpsValue :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code (F a) -> (t a -> t R) -> t R
toCpsValue lenv env a@(Callcc.ApplyCode f x) k =
  let F t = Callcc.typeOf a
      x' = toCpsData lenv env x
   in toCpsFn lenv env f x' $ Cps.letTo t k
toCpsValue lenv env (Callcc.LetBeCode value binder body) k =
  Cps.letBe (toCpsData lenv env value) $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCpsValue lenv env' body k
toCpsValue lenv env (Callcc.LetToCode action binder body) k =
  toCpsValue lenv env action $ \x ->
    let env' = VarMap.insert binder (Y x) env
     in toCpsValue lenv env' body k
toCpsValue lenv env (Callcc.ReturnCode value) k = k (toCpsData lenv env value)
toCpsValue lenv env (Callcc.CatchCode binder@(Label (F t) _) body) k =
  Cps.letBe (Cps.letTo t k) $ \k' ->
    let lenv' = LabelMap.insert binder (L k') lenv
     in toCpsR lenv' env body

toCpsR :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code R -> t R
toCpsR lenv env (Callcc.ForceCode thunk stack) =
  Cps.letBe (toCpsData lenv env stack) $ \k ->
    Cps.letBe (toCpsData lenv env thunk) $ \th ->
      Cps.force th k
toCpsR lenv env (Callcc.ThrowCode k body) =
  let k' = toCpsData lenv env k
   in toCps lenv env body k'
toCpsR lenv env (Callcc.ApplyCode f x) =
  let x' = toCpsData lenv env x
   in toCpsFn lenv env f x' Cps.nilStack
toCpsR lenv env (Callcc.LetBeCode value binder body) =
  Cps.letBe (toCpsData lenv env value) $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCpsR lenv env' body
toCpsR lenv env (Callcc.LetToCode action binder body) =
  toCpsValue lenv env action $ \x ->
    let env' = VarMap.insert binder (Y x) env
     in toCpsR lenv env' body

toCpsFn :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code (a :=> b) -> t a -> t (Stack b) -> t R
toCpsFn lenv env a@(Callcc.ApplyCode f x) y k =
  let x' = toCpsData lenv env x
   in toCpsFn lenv env f x' $ Cps.push y k
toCpsFn lenv env (Callcc.LetBeCode value binder body) x k =
  Cps.letBe (toCpsData lenv env value) $ \val ->
    let env' = VarMap.insert binder (Y val) env
     in toCpsFn lenv env' body x k
toCpsFn lenv env (Callcc.LambdaCode binder body) x k =
  Cps.letBe x $ \x' ->
    let env' = VarMap.insert binder (Y x') env
     in toCps lenv env' body k
toCpsFn lenv env (Callcc.LetToCode action binder body) x k =
  toCpsValue lenv env action $ \y ->
    let env' = VarMap.insert binder (Y y) env
     in toCpsFn lenv env' body x k
toCpsFn lenv env (Callcc.CatchCode binder@(Label (a :=> b) _) body) x k =
  Cps.letBe x $ \x' ->
    Cps.letBe k $ \k' ->
      let lenv' = LabelMap.insert binder (L (Cps.push x' k')) lenv
       in toCpsR lenv' env body

toCps :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (Stack a) -> t R
toCps lenv env val k =
  case Callcc.typeOf val of
    R -> toCpsR lenv env val
    F _ -> toCpsValue lenv env val $ \x -> Cps.apply k x
    a :=> _ ->
      Cps.pop k $ \t ->
        Cps.letTo a $ \h ->
          toCpsFn lenv env val h t

newtype L t a = L (t (Stack a))

newtype Y t a = Y (t a)

toCpsData :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Data a -> t a
toCpsData _ _ (Callcc.ConstantData x) = Cps.constant x
toCpsData _ _ (Callcc.GlobalData x) = Cps.global x
toCpsData _ env (Callcc.VariableData v) =
  let Just (Y x) = VarMap.lookup v env
   in x
toCpsData lenv _ (Callcc.LabelData v) =
  let Just (L x) = LabelMap.lookup v lenv
   in x
toCpsData lenv env (Callcc.ThunkData label@(Label t _) body) =
  Cps.thunk t $ \k ->
    let lenv' = LabelMap.insert label (L k) lenv
     in toCpsR lenv' env body
