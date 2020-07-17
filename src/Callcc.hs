{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (build, Builder (..), Callcc (..), Stack, Code, Data, simplify, abstractCode, abstractData) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Explicit
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasStack
import HasThunk
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import qualified Pure
import Tuple
import qualified Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

class (HasStack t, HasGlobals t, HasConstants t, HasLet t, HasThunk t, Explicit t, Tuple t, Pure.Pure t) => Callcc t where
  catch :: SAlgebra a -> (StackRep t a -> CodeRep t Void) -> CodeRep t a
  throw :: StackRep t a -> CodeRep t a -> CodeRep t Void

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Stack (a :=> b) -> Variable a -> Label b -> Code c -> Code c
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

build :: CodeRep Builder a -> Code a
build (CB _ s) = Unique.run s

data Builder

instance HasCode Builder where
  data CodeRep Builder a = CB (SAlgebra a) (Unique.State (Code a))

instance HasData Builder where
  data DataRep Builder a = DB (SSet a) (Unique.State (Data a))

instance HasGlobals Builder where
  global g@(Global t _) = CB t $ pure (GlobalCode g)

instance HasConstants Builder where
  constant k = DB (Constant.typeOf k) $ pure (ConstantData k)
  unit = DB SUnit $ pure UnitData

instance Pure.Pure Builder where
  pure (DB t value) = CB (SF t) $ pure ReturnCode <*> value

instance HasLet Builder where
  letBe x@(DB t xs) f =
    let CB bt _ = f (DB t (pure undefined))
     in CB bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v)
          body' <- body
          pure $ LetBeCode x' v body'

instance Explicit Builder where
  letTo x@(CB (SF t) xs) f =
    let CB bt _ = f (DB t (pure undefined))
     in CB bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v)
          body' <- body
          pure $ LetToCode x' v body'
  apply (CB (_ `SFn` b) f) (DB _ x) =
    CB b $
      pure ApplyCode <*> f <*> x

instance Tuple Builder

instance HasStack Builder where
  data StackRep Builder a = SB (SAlgebra a) (Unique.State (Stack a))

instance HasThunk Builder where
  lambda (SB (t `SFn` result) k) f =
    let CB bt _ = f ((DB t . pure) $ undefined) ((SB result . pure) $ undefined)
     in CB bt $ do
          v <- pure (Variable t) <*> Unique.uniqueId
          l <- pure (Label result) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v) ((SB result . pure) $ LabelStack l)
          body' <- body
          k' <- k
          pure $ LambdaCode k' v l body'
  thunk t f = DB (SU t) $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ ThunkData v body'
  force (DB _ thunk) (SB _ stack) =
    CB SVoid $
      pure ForceCode <*> thunk <*> stack

instance Callcc Builder where
  catch t f = CB t $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ CatchCode v body'
  throw (SB _ x) (CB _ f) =
    CB SVoid $
      pure ThrowCode <*> x <*> f

abstractCode :: Callcc t => Code a -> CodeRep t a
abstractCode = abstractCode' LabelMap.empty VarMap.empty

abstractData :: Callcc t => Data a -> DataRep t a
abstractData = abstractData' LabelMap.empty VarMap.empty

abstractCode' :: Callcc t => LabelMap (StackRep t) -> VarMap (DataRep t) -> Code a -> CodeRep t a
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
  LambdaCode k binder@(Variable t _) lbl@(Label n _) body ->
    lambda (abstractStack lenv env k) $ \x n ->
      let env' = VarMap.insert binder x env
          lenv' = LabelMap.insert lbl n lenv
       in abstractCode' lenv' env' body
  ReturnCode val -> Pure.pure (abstractData' lenv env val)
  GlobalCode g -> global g
  CatchCode lbl@(Label t _) body -> catch t $ \stk ->
    let lenv' = LabelMap.insert lbl stk lenv
     in abstractCode' lenv' env body
  ThrowCode k value -> throw (abstractStack lenv env k) (abstractCode' lenv env value)
  ForceCode thunk (LabelStack lbl) -> case LabelMap.lookup lbl lenv of
    Just stk -> force (abstractData' lenv env thunk) stk

abstractStack :: Callcc t => LabelMap (StackRep t) -> VarMap (DataRep t) -> Stack x -> StackRep t x
abstractStack lenv _ (LabelStack lbl) = case LabelMap.lookup lbl lenv of
  Just stk -> stk

abstractData' :: Callcc t => LabelMap (StackRep t) -> VarMap (DataRep t) -> Data x -> DataRep t x
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
  PairData h t -> pair (abstractData' lenv env h) (abstractData' lenv env t)

simplify :: Code a -> Code a
simplify = simpCode

simpCode :: Code a -> Code a
simpCode code = case code of
  LetToCode (ReturnCode value) binder body -> simpCode (LetBeCode value binder body)
  LambdaCode k binder lbl body -> LambdaCode k binder lbl (simpCode body)
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
  PairData x y -> PairData (simpData x) (simpData y)
  ThunkData label body -> ThunkData label (simpCode body)
  g@(ConstantData _) -> g
  g@(VariableData _) -> g
