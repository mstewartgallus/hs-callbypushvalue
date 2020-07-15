{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (build, Builder (..), Callcc (..), Stack (..), Code (..), Data (..), typeOf, inline, simplify, abstractCode, abstractData) where

import Basic
import Common
import Const
import Constant (Constant)
import qualified Constant
import Core
import Data.Text as T
import Global
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import qualified TextShow (Builder)
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
  TailData tuple ->
    let t `SPair` _ = typeOfData tuple
     in t
  PushData h t -> typeOfData h `SPair` typeOfData t

build :: AlgRep Builder a -> Code a
build (CB _ s) = Unique.run s

data Builder

instance Basic Builder where
  data AlgRep Builder a = CB (SAlg a) (Unique.State (Code a))
  global g@(Global t _) = CB t $ pure (GlobalCode g)

instance Const Builder where
  data SetRep Builder a = DB (SSet a) (Unique.State (Data a))
  constant k = DB (Constant.typeOf k) $ pure (ConstantData k)

instance Callcc Builder where
  data StackRep Builder a = SB (SAlg a) (Unique.State (Stack a))

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
  unit = DB SUnit $ pure UnitData
  apply (CB (_ `SFn` b) f) (DB _ x) =
    CB b $
      pure ApplyCode <*> f <*> x

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
  TailData tuple -> Callcc.tail (abstractData' lenv env tuple)
  PushData h t -> push (abstractData' lenv env h) (abstractData' lenv env t)

class (Basic t, Const t) => Callcc t where
  data StackRep t :: Alg -> *

  returns :: SetRep t a -> AlgRep t (F a)
  letTo :: AlgRep t (F a) -> (SetRep t a -> AlgRep t b) -> AlgRep t b
  letBe :: SetRep t a -> (SetRep t a -> AlgRep t b) -> AlgRep t b

  lambda :: SSet a -> (SetRep t a -> AlgRep t b) -> AlgRep t (a :=> b)
  apply :: AlgRep t (a :=> b) -> SetRep t a -> AlgRep t b

  unit :: SetRep t Unit

  push :: SetRep t a -> SetRep t b -> SetRep t (a :*: b)
  tail :: SetRep t (a :*: b) -> SetRep t a
  head :: SetRep t (a :*: b) -> SetRep t b

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

-- HeadCode :: Data (a :*: b) -> Code a

data Stack a where
  LabelStack :: Label a -> Stack a

data Data a where
  UnitData :: Data Unit
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code Void -> Data (U a)
  PushData :: Data a -> Data b -> Data (a :*: b)
  TailData :: Data (a :*: b) -> Data a

data View

instance Basic View where
  newtype AlgRep View a = V (forall s. Unique.Stream s -> TextShow.Builder)
  global g = V $ \_ -> showb g

instance Const View where
  data SetRep View a = VS (forall s. Unique.Stream s -> TextShow.Builder)
  constant k = VS $ \_ -> showb k

instance Callcc View where
  data StackRep View a = VStk (forall s. Unique.Stream s -> TextShow.Builder)

  unit = VS $ \_ -> fromString "."

  returns (VS value) = V $ \s -> fromString "return " <> value s

  letTo (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (VS $ \_ -> binder)
     in x xs <> fromString " to " <> binder <> fromString ".\n" <> y ys
  letBe (VS x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (VS $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = V $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        V body = f (VS $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  apply (V f) (VS x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n" <> f fs

  catch t f = V $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        V body = f (VStk $ \_ -> binder)
     in fromString "catch " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  thunk t f = VS $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        V body = f (VStk $ \_ -> binder)
     in fromString "thunk " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s

  throw (VStk f) (V x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\nthrow " <> f fs
  force (VS f) (VStk x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n! " <> f fs

instance TextShow (Code a) where
  showb term = case abstractCode term of
    V b -> Unique.withStream b

instance TextShow (Data a) where
  showb term = case abstractData term of
    VS b -> Unique.withStream b

instance TextShow (Stack a) where
  showb (LabelStack b) = showb b

indent :: TextShow.Builder -> TextShow.Builder
indent body = fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> body)))

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
  TailData tuple -> TailData (simpData tuple)
  PushData x y -> PushData (simpData x) (simpData y)
  ThunkData label body -> ThunkData label (simpCode body)
  g@(ConstantData _) -> g
  g@(VariableData _) -> g

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code c = case c of
      LetBeCode x binder body -> value x + code body
      LetToCode action binder body -> code action + code body
      LambdaCode binder body -> code body
      ApplyCode f x -> code f + value x
      ThrowCode _ f -> code f
      ForceCode x _ -> value x
      CatchCode _ body -> code body
      ReturnCode x -> value x
      _ -> 0
    value :: Data x -> Int
    value x = case x of
      VariableData binder -> if AnyVariable v == AnyVariable binder then 1 else 0
      PushData x y -> value x + value y
      TailData tuple -> value tuple
      ThunkData _ body -> code body
      _ -> 0

inline :: Callcc t => Code a -> AlgRep t a
inline = inlCode LabelMap.empty VarMap.empty

inlCode :: Callcc t => LabelMap (StackRep t) -> VarMap (SetRep t) -> Code a -> AlgRep t a
inlCode lenv env code = case code of
  LetBeCode term binder body ->
    let term' = inlValue lenv env term
     in if Callcc.count binder body <= 1
          then inlCode lenv (VarMap.insert binder term' env) body
          else letBe term' $ \x ->
            inlCode lenv (VarMap.insert binder x env) body
  LetToCode term binder body -> letTo (inlCode lenv env term) $ \x ->
    inlCode lenv (VarMap.insert binder x env) body
  ApplyCode f x -> apply (inlCode lenv env f) (inlValue lenv env x)
  LambdaCode binder@(Variable t _) body -> lambda t $ \x ->
    inlCode lenv (VarMap.insert binder x env) body
  ReturnCode val -> returns (inlValue lenv env val)
  ThrowCode x f -> throw (inlStack lenv env x) (inlCode lenv env f)
  CatchCode binder@(Label t _) body -> catch t $ \x ->
    inlCode (LabelMap.insert binder x lenv) env body
  ForceCode x f -> force (inlValue lenv env x) (inlStack lenv env f)
  GlobalCode g -> global g

inlValue :: Callcc t => LabelMap (StackRep t) -> VarMap (SetRep t) -> Data x -> SetRep t x
inlValue lenv env x = case x of
  VariableData v ->
    let Just r = VarMap.lookup v env
     in r
  ConstantData k -> constant k
  ThunkData binder@(Label t _) body -> thunk t $ \x ->
    inlCode (LabelMap.insert binder x lenv) env body
  PushData x y -> push (inlValue lenv env x) (inlValue lenv env y)
  TailData tuple -> Callcc.tail (inlValue lenv env tuple)
  UnitData -> Callcc.unit

inlStack :: Callcc t => LabelMap (StackRep t) -> VarMap (SetRep t) -> Stack x -> StackRep t x
inlStack lenv _ (LabelStack l) =
  let Just x = LabelMap.lookup l lenv
   in x
