{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Callcc (build, Builder (..), Callcc (..), Stack (..), Code (..), Data (..), typeOf, inline, simplify, abstractCode, abstractData) where

import Common
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
import Type
import Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

typeOf :: Code a -> Action a
typeOf x = case x of
  LambdaCode (Variable t _) body -> t :=> typeOf body
  ReturnCode value -> F (typeOfData value)
  LetBeCode _ _ body -> typeOf body
  LetToCode _ _ body -> typeOf body
  CatchCode (Label t _) _ -> t
  ApplyCode f _ ->
    let _ :=> result = typeOf f
     in result
  ThrowCode _ _ -> VoidType
  GlobalCode (Global t _) -> t

typeOfData :: Data a -> Type a
typeOfData x = case x of
  VariableData (Variable t _) -> t
  ConstantData k -> Constant.typeOf k
  ThunkData (Label t _) _ -> U t
  TailData tuple ->
    let t :*: _ = typeOfData tuple
     in t
  PushData h t -> typeOfData h :*: typeOfData t

data Builder t a where
  CB :: Action a -> Unique.State (Code a) -> Builder Code a
  DB :: Type a -> Unique.State (Data a) -> Builder Data a
  SB :: Action a -> Unique.State (Stack a) -> Builder Stack a

build :: Builder t a -> t a
build (CB _ s) = Unique.run s
build (DB _ s) = Unique.run s
build (SB _ s) = Unique.run s

instance Callcc Builder where
  global g@(Global t _) = CB t $ pure (GlobalCode g)
  returns (DB t value) = CB (F t) $ pure ReturnCode <*> value
  letTo x@(CB (F t) xs) f =
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
     in CB (t :=> result) $ do
          v <- pure (Variable t) <*> Unique.uniqueId
          let CB _ body = f ((DB t . pure) $ VariableData v)
          body' <- body
          pure $ LambdaCode v body'
  unit = DB UnitType $ pure UnitData
  apply (CB (_ :=> b) f) (DB _ x) =
    CB b $
      pure ApplyCode <*> f <*> x
  constant k = DB (Constant.typeOf k) $ pure (ConstantData k)

  thunk t f = DB (U t) $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ ThunkData v body'
  force (DB _ thunk) (SB _ stack) =
    CB VoidType $
      pure ForceCode <*> thunk <*> stack

  catch t f = CB t $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CB _ body = f ((SB t . pure) $ LabelStack v)
    body' <- body
    pure $ CatchCode v body'
  throw (SB _ x) (CB _ f) =
    CB VoidType $
      pure ThrowCode <*> x <*> f

abstractCode :: (Callcc t) => Code a -> t Code a
abstractCode = abstractCode' VarMap.empty

abstractData :: (Callcc t) => Data a -> t Data a
abstractData = abstractData' VarMap.empty

abstractCode' :: (Callcc t) => VarMap (t Data) -> Code a -> t Code a
abstractCode' env code = case code of
  LetBeCode term binder body -> letBe (abstractData' env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  LetToCode term binder body -> letTo (abstractCode' env term) $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  ApplyCode f x ->
    let f' = abstractCode' env f
        x' = abstractData' env x
     in apply f' x'
  LambdaCode binder@(Variable t _) body -> lambda t $ \x ->
    let env' = VarMap.insert binder x env
     in abstractCode' env' body
  ReturnCode val -> returns (abstractData' env val)
  GlobalCode g -> global g

abstractData' :: (Callcc t) => VarMap (t Data) -> Data x -> t Data x
abstractData' env x = case x of
  VariableData v@(Variable t u) ->
    case VarMap.lookup v env of
      Just x -> x
      Nothing -> error ("could not find var " ++ show u ++ " of type " ++ show t)
  ConstantData k -> constant k
  UnitData -> unit
  TailData tuple -> Callcc.tail (abstractData' env tuple)
  PushData h t -> push (abstractData' env h) (abstractData' env t)

class Callcc t where
  constant :: Constant a -> t Data a
  global :: Global a -> t Code a
  returns :: t Data a -> t Code (F a)
  letTo :: t Code (F a) -> (t Data a -> t Code b) -> t Code b
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b

  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a :=> b)
  apply :: t Code (a :=> b) -> t Data a -> t Code b

  unit :: t Data Unit

  push :: t Data a -> t Data b -> t Data (a :*: b)
  tail :: t Data (a :*: b) -> t Data a
  head :: t Data (a :*: b) -> t Data b

  catch :: Action a -> (t Stack a -> t Code Void) -> t Code a
  throw :: t Stack a -> t Code a -> t Code Void

  thunk :: Action a -> (t Stack a -> t Code Void) -> t Data (U a)
  force :: t Data (U a) -> t Stack a -> t Code Void

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

instance TextShow (Code a) where
  showb code = case code of
    GlobalCode g -> showb g
    LambdaCode binder@(Variable t _) body -> fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
    ApplyCode f x -> showb x <> fromString "\n" <> showb f
    ReturnCode value -> fromString "return " <> showb value
    LetToCode action binder body -> showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
    LetBeCode value binder body -> showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
    CatchCode binder@(Label t _) body ->
      fromString "catch " <> showb binder <> fromString ": " <> showb t <> fromString " {" <> indent (showb body) <> fromString "\n}"
    ThrowCode label body -> showb body <> fromString "\nthrow " <> showb label
    ForceCode thunk stack -> fromString "! " <> showb thunk <> fromString " " <> showb stack

instance TextShow (Data a) where
  showb x = case x of
    UnitData -> fromString "."
    ThunkData binder@(Label t _) body ->
      fromString "thunk " <> showb binder <> fromString ": " <> showb t <> indent (showb body) <> fromString "\n}"
    ConstantData k -> showb k
    VariableData b -> showb b
    TailData tuple -> showb tuple <> fromString "\ntail"
    PushData h t -> showb h <> fromString ", " <> showb t

indent :: TextShow.Builder -> TextShow.Builder
indent body = fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> body)))

instance TextShow (Stack a) where
  showb (LabelStack b) = showb b

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

inline :: Callcc t => Code a -> t Code a
inline = inlCode LabelMap.empty VarMap.empty

newtype L t a = L (t Stack a)

inlCode :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Code a -> t Code a
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
    inlCode (LabelMap.insert binder (L x) lenv) env body
  ForceCode x f -> force (inlValue lenv env x) (inlStack lenv env f)
  GlobalCode g -> global g

inlValue :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Data x -> t Data x
inlValue lenv env x = case x of
  VariableData v ->
    let Just r = VarMap.lookup v env
     in r
  ConstantData k -> constant k
  ThunkData binder@(Label t _) body -> thunk t $ \x ->
    inlCode (LabelMap.insert binder (L x) lenv) env body
  PushData x y -> push (inlValue lenv env x) (inlValue lenv env y)
  TailData tuple -> Callcc.tail (inlValue lenv env tuple)
  UnitData -> Callcc.unit

inlStack :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Stack x -> t Stack x
inlStack lenv _ (LabelStack l) =
  let Just (L x) = LabelMap.lookup l lenv
   in x
