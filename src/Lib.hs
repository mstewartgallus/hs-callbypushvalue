{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
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
import qualified Constant
import Core
import qualified Cps
import Global
import Label
import qualified LabelMap
import LabelMap (LabelMap)
import qualified SystemF
import Type
import qualified VarMap
import VarMap (VarMap)
import Variable

toCallByPushValue :: Cbpv.Cbpv t => SystemF.Term a -> t Cbpv.Code a
toCallByPushValue term =
  let ToCbpv x = SystemF.abstract term
   in x

newtype ToCbpv t a = ToCbpv (t Cbpv.Code a)

instance Cbpv.Cbpv t => SystemF.SystemF (ToCbpv t) where
  constant k = ToCbpv $ Cbpv.returns (Cbpv.constant k)
  global g = ToCbpv $ Cbpv.global g
  pair (ToCbpv x) (ToCbpv y) = ToCbpv $ Cbpv.returns (Cbpv.push (Cbpv.delay x) (Cbpv.push (Cbpv.delay y) Cbpv.unit))

  -- first (ToCbpv tuple) = ToCbpv x
  -- second (ToCbpv tuple) = ToCbpv y
  letBe (ToCbpv x) f = ToCbpv $ Cbpv.letBe (Cbpv.delay x) $ \x' ->
    let ToCbpv body = f (ToCbpv (Cbpv.force x'))
     in body
  lambda t f = ToCbpv $ Cbpv.lambda (U t) $ \x ->
    let ToCbpv body = f (ToCbpv (Cbpv.force x))
     in body
  apply (ToCbpv f) (ToCbpv x) = ToCbpv $ Cbpv.apply f (Cbpv.delay x)

toCallcc :: Cbpv.Code a -> Callcc.Code a
toCallcc code =
  let CodeCallcc _ x = Cbpv.abstractCode code
   in Callcc.build x

data ToCallcc t tag a where
  DataCallcc :: Type a -> t Callcc.Data a -> ToCallcc t Cbpv.Data a
  CodeCallcc :: Action a -> t Callcc.Code a -> ToCallcc t Cbpv.Code a

instance Callcc.Callcc t => Cbpv.Cbpv (ToCallcc t) where
  constant k = DataCallcc (Constant.typeOf k) $ Callcc.constant k
  global g@(Global t _) = CodeCallcc t $ Callcc.global g
  letBe (DataCallcc t x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ Callcc.letBe x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  letTo (CodeCallcc (F t) x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ Callcc.letTo x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  lambda t f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc (t :=> bt) $ Callcc.lambda t $ \x ->
          let CodeCallcc _ body = f (DataCallcc t x)
           in body
  apply (CodeCallcc (_ :=> b) f) (DataCallcc _ x) = CodeCallcc b $ Callcc.apply f x
  returns (DataCallcc t x) = CodeCallcc (F t) $ Callcc.returns x

  force (DataCallcc (U t) thunk) = CodeCallcc t $ Callcc.catch t (Callcc.force thunk)
  delay (CodeCallcc t code) = DataCallcc (U t) $ Callcc.thunk t $ \x ->
    Callcc.throw x code

toContinuationPassingStyle :: Cps.Cps t => Callcc.Code a -> t (Cps.Data (U a))
toContinuationPassingStyle = toCpsThunk LabelMap.empty VarMap.empty

toCpsThunk :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (Cps.Data (U a))
toCpsThunk lenv env act =
  let t = Callcc.typeOf act
   in Cps.thunk t $ \k -> toCps lenv env act k

toCps :: Cps.Cps t => LabelMap (L t) -> VarMap (Y t) -> Callcc.Code a -> t (Cps.Stack a) -> t Cps.Code
toCps lenv env (Callcc.ReturnCode x) k =
  let x' = toCpsData lenv env x
   in Cps.throw k x'
toCps lenv env (Callcc.ApplyCode f x) k =
  let x' = toCpsData lenv env x
   in toCps lenv env f (Cps.apply x' k)
toCps lenv env (Callcc.LetBeCode value binder@(Variable t _) body) k =
  Cps.throw
    ( Cps.letTo t $ \val ->
        let env' = VarMap.insert binder (Y val) env
         in toCps lenv env' body k
    )
    (toCpsData lenv env value)
toCps lenv env (Callcc.LambdaCode binder@(Variable t _) body) k =
  let a = Callcc.typeOf body
   in Cps.lambda k $ \x t ->
        let env' = VarMap.insert binder (Y x) env
         in toCps lenv env' body t
toCps lenv env (Callcc.LetToCode action binder@(Variable t _) body) k =
  toCps lenv env action $ Cps.letTo t $ \y ->
    let env' = VarMap.insert binder (Y y) env
     in toCps lenv env' body k
toCps lenv env (Callcc.CatchCode binder@(Label t _) body) k =
  Cps.force
    ( Cps.thunk t $ \k' ->
        let lenv' = LabelMap.insert binder (L k') lenv
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
     in toCps lenv' env body Cps.nil
