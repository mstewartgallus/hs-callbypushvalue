{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lib (toContinuationPassingStyle) where

import Basic
import qualified Callcc
import Common
import Const
import qualified Constant
import Core
import qualified Cps
import Explicit
import Global
import Label
import qualified LabelMap
import LabelMap (LabelMap)
import Tuple
import qualified VarMap
import VarMap (VarMap)
import Variable

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code a -> SetRep t (U a)
toContinuationPassingStyle = toCpsThunk LabelMap.empty VarMap.empty

toCpsThunk :: Cps.Cps t => LabelMap (Cps.StackRep t) -> VarMap (SetRep t) -> Callcc.Code a -> SetRep t (U a)
toCpsThunk lenv env act =
  let t = Callcc.typeOf act
   in Cps.thunk t $ \k -> toCps lenv env act k

toCps :: Cps.Cps t => LabelMap (Cps.StackRep t) -> VarMap (SetRep t) -> Callcc.Code a -> Cps.StackRep t a -> Cps.CodeRep t
toCps lenv env (Callcc.ReturnCode x) k =
  let x' = toCpsData lenv env x
   in Cps.throw k x'
toCps lenv env (Callcc.ApplyCode f x) k =
  let x' = toCpsData lenv env x
   in toCps lenv env f (Cps.apply x' k)
toCps lenv env (Callcc.LetBeCode value binder@(Variable t _) body) k =
  Cps.throw
    ( Cps.letTo t $ \val ->
        let env' = VarMap.insert binder val env
         in toCps lenv env' body k
    )
    (toCpsData lenv env value)
toCps lenv env (Callcc.LambdaCode binder@(Variable t _) body) k =
  let a = Callcc.typeOf body
   in Cps.lambda k $ \x t ->
        let env' = VarMap.insert binder x env
         in toCps lenv env' body t
toCps lenv env (Callcc.LetToCode action binder@(Variable t _) body) k =
  toCps lenv env action $ Cps.letTo t $ \y ->
    let env' = VarMap.insert binder y env
     in toCps lenv env' body k
toCps lenv env (Callcc.CatchCode binder@(Label t _) body) k =
  Cps.force
    ( Cps.thunk t $ \k' ->
        let lenv' = LabelMap.insert binder k' lenv
         in toCps lenv' env body Cps.nil
    )
    k
toCps _ _ (Callcc.GlobalCode x) k = Cps.global x k
toCps lenv env (Callcc.ForceCode thunk stack) _ =
  Cps.force (toCpsData lenv env thunk) (toCpsStack lenv env stack)
toCps lenv env (Callcc.ThrowCode k body) _ =
  toCps lenv env body (toCpsStack lenv env k)

-- toCps lenv env (Callcc.HeadCode tuple) k =
--   let tuple' = toCpsData lenv env tuple
--    in Cps.head tuple' k

toCpsStack :: Cps.Cps t => LabelMap (Cps.StackRep t) -> VarMap (SetRep t) -> Callcc.Stack a -> Cps.StackRep t a
toCpsStack lenv _ (Callcc.LabelStack v) =
  let Just x = LabelMap.lookup v lenv
   in x

toCpsData :: Cps.Cps t => LabelMap (Cps.StackRep t) -> VarMap (SetRep t) -> Callcc.Data a -> SetRep t a
toCpsData _ _ (Callcc.ConstantData x) = constant x
toCpsData _ env (Callcc.VariableData v) =
  let Just x = VarMap.lookup v env
   in x
toCpsData lenv env (Callcc.ThunkData label@(Label t _) body) =
  Cps.thunk t $ \k ->
    let lenv' = LabelMap.insert label k lenv
     in toCps lenv' env body Cps.nil
