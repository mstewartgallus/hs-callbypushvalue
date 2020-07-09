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
import qualified SystemF
import Type
import qualified VarMap
import VarMap (VarMap)
import Variable

toCallByPushValue :: Cbpv.Cbpv t => SystemF.Term a -> t Cbpv.Code a
toCallByPushValue = toCbpv VarMap.empty

toCbpv :: Cbpv.Cbpv t => VarMap (t Cbpv.Data) -> SystemF.Term a -> t Cbpv.Code a
toCbpv env (SystemF.VariableTerm x) =
  let Just replacement = VarMap.lookup x env
   in Cbpv.force replacement
toCbpv _ (SystemF.ConstantTerm x) = Cbpv.returns (Cbpv.constant x)
toCbpv _ (SystemF.GlobalTerm x) = Cbpv.force (Cbpv.global x)
toCbpv env (SystemF.LetTerm term binder body) =
  let term' = toCbpv env term
   in Cbpv.letBe (Cbpv.delay term') $ \value ->
        let env' = VarMap.insert binder value env
         in toCbpv env' body
toCbpv env (SystemF.LambdaTerm binder@(Variable t _) body) =
  Cbpv.lambda t $ \value ->
    let env' = VarMap.insert binder value env
     in toCbpv env' body
toCbpv env (SystemF.ApplyTerm f x) =
  let f' = toCbpv env f
      x' = toCbpv env x
   in Cbpv.apply f' (Cbpv.delay x')

toCallcc :: Cbpv.Data a -> Callcc.Code (F a)
toCallcc x = Callcc.build $ toExplicitCatchThrowData VarMap.empty x

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
          Callcc.throw t val (Callcc.returns v)

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
              Callcc.throw (F (StackType t)) returner (Callcc.returns label)
          )
          $ \binder -> Callcc.throw (F (StackType (F (StackType t)))) binder code'

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code (F a) -> t (U (F a))
toContinuationPassingStyle = toCps' VarMap.empty

toCps' :: Cps.Cps t => VarMap (Y t) -> Callcc.Code (F a) -> t (U (F a))
toCps' env act =
  let t = Callcc.typeOf act
   in Cps.letTo (StackType t) $ \k ->
        toCpsValue env act $ \x -> Cps.returns x k

toCpsValue :: Cps.Cps t => VarMap (Y t) -> Callcc.Code (F a) -> (t a -> t R) -> t R
toCpsValue env a@(Callcc.ApplyCode f x) k =
  let F t = Callcc.typeOf a
      x' = toCpsData env x
   in toCpsFn env f x' $ Cps.letTo t k
toCpsValue env (Callcc.LetBeCode value binder body) k =
  Cps.letBe (toCpsData env value) $ \value ->
    let env' = VarMap.insert binder (Y value) env
     in toCpsValue env' body k
toCpsValue env (Callcc.LetToCode action binder body) k =
  toCpsValue env action $ \x ->
    let env' = VarMap.insert binder (Y x) env
     in toCpsValue env' body k
toCpsValue env (Callcc.ReturnCode value) k = k (toCpsData env value)
toCpsValue env (Callcc.ThrowCode _ k body) _ =
  let k' = toCpsData env k
   in toCps env body k'
toCpsValue env (Callcc.CatchCode binder@(Variable (StackType (F t)) _) body) k =
  Cps.letBe (Cps.letTo t k) $ \k' ->
    let env' = VarMap.insert binder (Y k') env
     in toCpsValue env' body $ \x -> Cps.returns x k'

toCpsFn :: Cps.Cps t => VarMap (Y t) -> Callcc.Code (a :=> b) -> t a -> t (Stack b) -> t R
toCpsFn env a@(Callcc.ApplyCode f x) y k =
  let x' = toCpsData env x
   in toCpsFn env f x' $ Cps.push y k
toCpsFn env (Callcc.LetBeCode value binder body) x k =
  Cps.letBe (toCpsData env value) $ \val ->
    let env' = VarMap.insert binder (Y val) env
     in toCpsFn env' body x k
toCpsFn env (Callcc.LambdaCode binder body) x k =
  Cps.letBe x $ \x' ->
    let env' = VarMap.insert binder (Y x') env
     in toCps env' body k
toCpsFn env (Callcc.LetToCode action binder body) x k =
  toCpsValue env action $ \y ->
    let env' = VarMap.insert binder (Y y) env
     in toCpsFn env' body x k
toCpsFn env (Callcc.ThrowCode _ k body) _ _ =
  let k' = toCpsData env k
   in toCps env body k'
toCpsFn env (Callcc.CatchCode binder@(Variable (StackType (a :=> b)) _) body) x k =
  Cps.letBe x $ \x' ->
    Cps.letBe k $ \k' ->
      let env' = VarMap.insert binder (Y (Cps.push x' k')) env
       in toCpsFn env' body x' k'

toCps :: Cps.Cps t => VarMap (Y t) -> Callcc.Code a -> t (Stack a) -> t R
toCps env val k =
  let
   in case Callcc.typeOf val of
        F _ -> toCpsValue env val $ \x -> Cps.returns x k
        _ :=> _ -> Cps.pop k $ \h t -> toCpsFn env val h t

newtype Y t a = Y (t a)

toCpsData :: Cps.Cps t => VarMap (Y t) -> Callcc.Data a -> t a
toCpsData _ (Callcc.ConstantData x) = Cps.constant x
toCpsData _ (Callcc.GlobalData x) = Cps.global x
toCpsData env (Callcc.VariableData v) =
  let Just (Y x) = VarMap.lookup v env
   in x
