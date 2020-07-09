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
toCallcc x = Callcc.build $ toExplicitCatchThrow VarMap.empty x

toExplicitCatchThrow :: Callcc.Callcc t => VarMap (t Callcc.Data) -> Cbpv.Code a -> t Callcc.Code a
toExplicitCatchThrow env (Cbpv.LambdaCode binder@(Variable t _) body) =
  Callcc.lambda t $ \x ->
    toExplicitCatchThrow (VarMap.insert binder x env) body
toExplicitCatchThrow env (Cbpv.ApplyCode f x) =
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
toExplicitCatchThrowData _ (Cbpv.GlobalData x) = Callcc.returns (Callcc.global x)
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
          $ \binder -> Callcc.throw binder code'

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code a -> t (U a)
toContinuationPassingStyle = toCps' LabelMap.empty VarMap.empty

toCps' :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (U a)
toCps' lenv env act =
  let t = Callcc.typeOf act
   in case t of
        F _ -> Cps.letTo (StackType t) $ \k ->
          toCpsValue lenv env act $ \x ->
            Cps.returns x k
        _ :=> _ -> Cps.letTo (StackType t) $ \k ->
          Cps.pop k $ \h t ->
            toCpsFn lenv env act h t

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
toCpsR lenv env (Callcc.ThrowCode k body) =
  let k' = toCpsData lenv env k
   in toCps lenv env body k'

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
    F _ -> toCpsValue lenv env val $ \x -> Cps.returns x k
    _ :=> _ -> Cps.pop k $ \h t -> toCpsFn lenv env val h t

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
