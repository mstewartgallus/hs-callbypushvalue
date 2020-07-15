{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lib
  ( toCallByPushValue,
    toCallcc,
    toContinuationPassingStyle,
  )
where

import Basic
import qualified Callcc
import qualified Cbpv
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
import qualified SystemF
import Type
import qualified VarMap
import VarMap (VarMap)
import Variable

toCallByPushValue :: SystemF.Term a -> Cbpv.Code a
toCallByPushValue term =
  let ToCbpv x = SystemF.abstract term
   in Cbpv.build x

data ToCbpv t

instance Basic t => Basic (ToCbpv t) where
  newtype AlgRep (ToCbpv t) a = ToCbpv (AlgRep t a)
  global g = ToCbpv (global g)

instance Cbpv.Cbpv t => SystemF.SystemF (ToCbpv t) where
  constant k = ToCbpv $ returns (constant k)
  pair (ToCbpv x) (ToCbpv y) = ToCbpv $ returns (Cbpv.push (Cbpv.thunk x) (Cbpv.thunk y))

  -- first (ToCbpv tuple) = ToCbpv x
  -- second (ToCbpv tuple) = ToCbpv y
  letBe (ToCbpv x) f = ToCbpv $ letBe (Cbpv.thunk x) $ \x' ->
    let ToCbpv body = f (ToCbpv (Cbpv.force x'))
     in body
  lambda t f = ToCbpv $ lambda (SU t) $ \x ->
    let ToCbpv body = f (ToCbpv (Cbpv.force x))
     in body
  ToCbpv f <*> ToCbpv x = ToCbpv $ apply f (Cbpv.thunk x)

toCallcc :: Cbpv.Code a -> Callcc.Code a
toCallcc code =
  let CodeCallcc _ x = Cbpv.abstractCode code
   in Callcc.build x

data ToCallcc t

instance Basic t => Basic (ToCallcc t) where
  data AlgRep (ToCallcc t) a = CodeCallcc (SAlg a) (AlgRep t a)
  global g@(Global t _) = CodeCallcc t (global g)

instance Const t => Const (ToCallcc t) where
  data SetRep (ToCallcc t) a = DataCallcc (SSet a) (SetRep t a)

  constant k = DataCallcc (Constant.typeOf k) $ constant k

instance Explicit t => Explicit (ToCallcc t) where
  letBe (DataCallcc t x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ letBe x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  letTo (CodeCallcc (SF t) x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ letTo x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  lambda t f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc (t `SFn` bt) $ lambda t $ \x ->
          let CodeCallcc _ body = f (DataCallcc t x)
           in body
  apply (CodeCallcc (_ `SFn` b) f) (DataCallcc _ x) = CodeCallcc b $ apply f x
  returns (DataCallcc t x) = CodeCallcc (SF t) $ returns x

instance Callcc.Callcc t => Cbpv.Cbpv (ToCallcc t) where
  force (DataCallcc (SU t) thunk) = CodeCallcc t $ Callcc.catch t (Callcc.force thunk)
  thunk (CodeCallcc t code) = DataCallcc (SU t) $ Callcc.thunk t $ \x ->
    Callcc.throw x code

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
