{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CallccSimplifier (Simplifier, simplifyExtract) where

import Callcc
import Common
import Constant (Constant)
import qualified Constant
import Core
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasLetTo
import HasReturn
import HasStack
import HasThunk
import HasTuple
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import qualified Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

simplifyExtract :: Callcc t => Code Simplifier a -> Code t a
simplifyExtract term = abstractC (simplify (build term))

data C a where
  GlobalC :: Global a -> S a -> C Void
  LambdaC :: S (a :=> b) -> Variable a -> Label b -> C c -> C c
  ApplyC :: C (a :=> b) -> D a -> C b
  ReturnC :: D a -> C (F a)
  LetBeC :: D a -> Variable a -> C b -> C b
  LetToC :: C (F a) -> Variable a -> C b -> C b
  CatchC :: Label a -> C Void -> C a
  ThrowC :: S a -> C a -> C Void
  ForceC :: D (U a) -> S a -> C Void

data S a where
  LabelStack :: Label a -> S a

data D a where
  UnitD :: D Unit
  ConstantD :: Constant a -> D a
  VariableD :: Variable a -> D a
  ThunkD :: Label a -> C Void -> D (U a)
  PairD :: D a -> D b -> D (a :*: b)

build :: Code Simplifier a -> C a
build (CB _ s) = Unique.run s

data Simplifier

instance HasCode Simplifier where
  data Code Simplifier a = CB (SAlgebra a) (Unique.State (C a))

instance HasData Simplifier where
  data Data Simplifier a = DB (SSet a) (Unique.State (D a))

instance HasConstants Simplifier where
  constant k = DB (Constant.typeOf k) $ pure (ConstantD k)
  unit = DB SUnit $ pure UnitD

instance HasReturn Simplifier where
  returns (DB t value) = CB (SF t) $ pure ReturnC <*> value

instance HasLet Simplifier where
  letBe x@(DB t vx) f =
    let CB bt _ = f x
     in CB bt $ do
          x' <- vx
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableD v)
          body' <- body
          pure $ LetBeC x' v body'

instance HasLetTo Simplifier where
  letTo x@(CB (SF t) xs) f =
    let CB bt _ = f (DB t (pure undefined))
     in CB bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableD v)
          body' <- body
          pure $ LetToC x' v body'
  apply (CB (_ `SFn` b) f) (DB _ x) =
    CB b $
      pure ApplyC <*> f <*> x

instance HasTuple Simplifier

instance HasStack Simplifier where
  data Stack Simplifier a = SB (SAlgebra a) (Unique.State (S a))

instance HasThunk Simplifier where
  call g (SB _ k) = CB SVoid $ do
    k' <- k
    pure (GlobalC g k')

  lambda (SB (t `SFn` result) k) f =
    let CB bt _ = f ((DB t . pure) $ undefined) ((SB result . pure) $ undefined)
     in CB bt $ do
          v <- pure (Variable t) <*> Unique.uniqueId
          l <- pure (Label result) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableD v) ((SB result . pure) $ LabelStack l)
          body' <- body
          k' <- k
          pure $ LambdaC k' v l body'
  thunk t f = DB (SU t) $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ ThunkD v body'
  force (DB _ thunk) (SB _ stack) =
    CB SVoid $
      pure ForceC <*> thunk <*> stack

instance Callcc Simplifier where
  catch t f = CB t $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ CatchC v body'
  throw (SB _ x) (CB _ f) =
    CB SVoid $
      pure ThrowC <*> x <*> f

abstractC :: Callcc t => C a -> Code t a
abstractC = abstractCode' LabelMap.empty VarMap.empty

abstractD :: Callcc t => D a -> Data t a
abstractD = abstractData' LabelMap.empty VarMap.empty

abstractCode' :: Callcc t => LabelMap (Stack t) -> VarMap (Data t) -> C a -> Code t a
abstractCode' lenv env code = case code of
  LetBeC term binder body -> letBe (abstractData' lenv env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' lenv env' body
  LetToC term binder body -> letTo (abstractCode' lenv env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' lenv env' body
  ApplyC f x ->
    let f' = abstractCode' lenv env f
        x' = abstractData' lenv env x
     in apply f' x'
  LambdaC k binder@(Variable t _) lbl@(Label n _) body ->
    lambda (abstractStack lenv env k) $ \x n ->
      let env' = VarMap.insert binder x env
          lenv' = LabelMap.insert lbl n lenv
       in abstractCode' lenv' env' body
  ReturnC val -> returns (abstractData' lenv env val)
  GlobalC g k -> call g (abstractStack lenv env k)
  CatchC lbl@(Label t _) body -> catch t $ \stk ->
    let lenv' = LabelMap.insert lbl stk lenv
     in abstractCode' lenv' env body
  ThrowC k value -> throw (abstractStack lenv env k) (abstractCode' lenv env value)
  ForceC thunk (LabelStack lbl) -> case LabelMap.lookup lbl lenv of
    Just stk -> force (abstractData' lenv env thunk) stk

abstractStack :: Callcc t => LabelMap (Stack t) -> VarMap (Data t) -> S x -> Stack t x
abstractStack lenv _ (LabelStack lbl) = case LabelMap.lookup lbl lenv of
  Just stk -> stk

abstractData' :: Callcc t => LabelMap (Stack t) -> VarMap (Data t) -> D x -> Data t x
abstractData' lenv env x = case x of
  ThunkD lbl@(Label t _) body -> thunk t $ \stk ->
    let lenv' = LabelMap.insert lbl stk lenv
     in abstractCode' lenv' env body
  VariableD v@(Variable t u) ->
    case VarMap.lookup v env of
      Just x -> x
      Nothing -> error ("could not find var " ++ show u ++ " of type")
  ConstantD k -> constant k
  UnitD -> unit
  PairD h t -> pair (abstractData' lenv env h) (abstractData' lenv env t)

simplify :: C a -> C a
simplify = simpC

simpC :: C a -> C a
simpC code = case code of
  LetToC (ReturnC value) binder body -> simpC (LetBeC value binder body)
  LambdaC k binder lbl body -> LambdaC k binder lbl (simpC body)
  ApplyC f x -> ApplyC (simpC f) (simpD x)
  LetBeC thing binder body -> LetBeC (simpD thing) binder (simpC body)
  LetToC act binder body -> LetToC (simpC act) binder (simpC body)
  CatchC binder body -> CatchC binder (simpC body)
  ThrowC stack act -> ThrowC stack (simpC act)
  ForceC th stk -> ForceC (simpD th) stk
  ReturnC x -> ReturnC (simpD x)
  g@(GlobalC _ _) -> g

simpD :: D a -> D a
simpD x = case x of
  UnitD -> UnitD
  PairD x y -> PairD (simpD x) (simpD y)
  ThunkD label body -> ThunkD label (simpC body)
  g@(ConstantD _) -> g
  g@(VariableD _) -> g
