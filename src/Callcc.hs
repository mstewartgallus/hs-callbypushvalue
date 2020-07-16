{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (build, Builder (..), Callcc (..), Stack (..), Code (..), Data (..), typeOf, simplify, abstractCode, abstractData) where

import Basic
import Common
import Const
import Constant (Constant)
import qualified Constant
import Core
import Data.Text as T
import Explicit
import Global
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import qualified TextShow (Builder)
import Tuple
import Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

typeOf :: Code a -> SAlg a
typeOf x = case x of
  LambdaCode (Variable t _) body -> t `SFn` typeOf body
  ReturnCode value -> SF (typeOfData value)
  LetBeCode _ _ body -> typeOf body
  LetToCode _ _ body -> typeOf body
  ApplyCode f _ ->
    let _ `SFn` result = typeOf f
     in result
  CatchCode (Label t _) _ -> t
  ThrowCode _ _ -> SVoid
  GlobalCode (Global t _) -> t

typeOfData :: Data a -> SSet a
typeOfData x = case x of
  VariableData (Variable t _) -> t
  ConstantData k -> Constant.typeOf k
  ThunkData (Label t _) _ -> SU t
  FirstData tuple ->
    let t `SPair` _ = typeOfData tuple
     in t
  PairData h t -> typeOfData h `SPair` typeOfData t

build :: AlgRep Builder a -> Code a
build (CB _ s) = Unique.run s

data Builder

instance Basic Builder where
  data AlgRep Builder a = CB (SAlg a) (Unique.State (Code a))
  global g@(Global t _) = CB t $ pure (GlobalCode g)

instance Const Builder where
  data SetRep Builder a = DB (SSet a) (Unique.State (Data a))
  constant k = DB (Constant.typeOf k) $ pure (ConstantData k)
  unit = DB SUnit $ pure UnitData

instance Explicit Builder where
  returns (DB t value) = CB (SF t) $ pure ReturnCode <*> value
  letTo x@(CB (SF t) xs) f =
    let CB bt _ = f (DB t (pure undefined))
     in CB bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v)
          body' <- body
          pure $ LetToCode x' v body'
  letBe x@(DB t xs) f =
    let CB bt _ = f (DB t (pure undefined))
     in CB bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v)
          body' <- body
          pure $ LetBeCode x' v body'
  lambda t f =
    let CB result _ = f (DB t (pure undefined))
     in CB (t `SFn` result) $ do
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v)
          body' <- body
          pure $ LambdaCode v body'
  apply (CB (_ `SFn` b) f) (DB _ x) =
    CB b $
      pure ApplyCode <*> f <*> x

instance Tuple Builder

instance Callcc Builder where
  data StackRep Builder a = SB (SAlg a) (Unique.State (Stack a))

  thunk t f = DB (SU t) $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ ThunkData v body'
  force (DB _ thunk) (SB _ stack) =
    CB SVoid $
      pure ForceCode <*> thunk <*> stack

  catch t f = CB t $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ CatchCode v body'
  throw (SB _ x) (CB _ f) =
    CB SVoid $
      pure ThrowCode <*> x <*> f

abstractCode :: Callcc t => Code a -> AlgRep t a
abstractCode = abstractCode' LabelMap.empty VarMap.empty

abstractData :: Callcc t => Data a -> SetRep t a
abstractData = abstractData' LabelMap.empty VarMap.empty

abstractCode' :: Callcc t => LabelMap (StackRep t) -> VarMap (SetRep t) -> Code a -> AlgRep t a
abstractCode' lenv env code = case code of
  LetBeCode term binder body -> letBe (abstractData' lenv env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' lenv env' body
  LetToCode term binder body -> letTo (abstractCode' lenv env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' lenv env' body
  ApplyCode f x ->
    let f' = abstractCode' lenv env f
        x' = abstractData' lenv env x
     in apply f' x'
  LambdaCode binder@(Variable t _) body -> lambda t $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' lenv env' body
  ReturnCode val -> returns (abstractData' lenv env val)
  GlobalCode g -> global g
  CatchCode lbl@(Label t _) body -> catch t $ \stk ->
    let lenv' = LabelMap.insert lbl stk lenv
     in abstractCode' lenv' env body
  ThrowCode (LabelStack lbl) value -> case LabelMap.lookup lbl lenv of
    Just stk -> throw stk (abstractCode' lenv env value)
  ForceCode thunk (LabelStack lbl) -> case LabelMap.lookup lbl lenv of
    Just stk -> force (abstractData' lenv env thunk) stk

abstractData' :: Callcc t => LabelMap (StackRep t) -> VarMap (SetRep t) -> Data x -> SetRep t x
abstractData' lenv env x = case x of
  ThunkData lbl@(Label t _) body -> thunk t $ \stk ->
    let lenv' = LabelMap.insert lbl stk lenv
     in abstractCode' lenv' env body
  VariableData v@(Variable t u) ->
    case VarMap.lookup v env of
      Just x -> x
      Nothing -> error ("could not find var " ++ show u ++ " of type")
  ConstantData k -> constant k
  UnitData -> unit
  FirstData tuple -> first (abstractData' lenv env tuple)
  PairData h t -> pair (abstractData' lenv env h) (abstractData' lenv env t)

class (Basic t, Const t, Explicit t, Tuple t) => Callcc t where
  data StackRep t :: Alg -> *

  catch :: SAlg a -> (StackRep t a -> AlgRep t Void) -> AlgRep t a
  throw :: StackRep t a -> AlgRep t a -> AlgRep t Void

  thunk :: SAlg a -> (StackRep t a -> AlgRep t Void) -> SetRep t (U a)
  force :: SetRep t (U a) -> StackRep t a -> AlgRep t Void

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a :=> b)
  ApplyCode :: Code (a :=> b) -> Data a -> Code b
  ReturnCode :: Data a -> Code (F a)
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  CatchCode :: Label a -> Code Void -> Code a
  ThrowCode :: Stack a -> Code a -> Code Void
  ForceCode :: Data (U a) -> Stack a -> Code Void

data Stack a where
  LabelStack :: Label a -> Stack a

data Data a where
  UnitData :: Data Unit
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code Void -> Data (U a)
  PairData :: Data a -> Data b -> Data (a :*: b)
  FirstData :: Data (a :*: b) -> Data a

simplify :: Code a -> Code a
simplify = simpCode

simpCode :: Code a -> Code a
simpCode code = case code of
  LetToCode (ReturnCode value) binder body -> simpCode (LetBeCode value binder body)
  ApplyCode (LambdaCode binder body) value -> simpCode (LetBeCode value binder body)
  LambdaCode binder body -> LambdaCode binder (simpCode body)
  ApplyCode f x -> ApplyCode (simpCode f) (simpData x)
  LetBeCode thing binder body -> LetBeCode (simpData thing) binder (simpCode body)
  LetToCode act binder body -> LetToCode (simpCode act) binder (simpCode body)
  CatchCode binder body -> CatchCode binder (simpCode body)
  ThrowCode stack act -> ThrowCode stack (simpCode act)
  ForceCode th stk -> ForceCode (simpData th) stk
  ReturnCode x -> ReturnCode (simpData x)
  g@(GlobalCode _) -> g

simpData :: Data a -> Data a
simpData x = case x of
  UnitData -> UnitData
  FirstData tuple -> FirstData (simpData tuple)
  PairData x y -> PairData (simpData x) (simpData y)
  ThunkData label body -> ThunkData label (simpCode body)
  g@(ConstantData _) -> g
  g@(VariableData _) -> g
