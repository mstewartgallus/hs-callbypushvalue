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
import Type
import Unique
import qualified VarMap
import VarMap (VarMap)
import Variable

typeOf :: Code a -> Action a
typeOf (LambdaCode (Variable t _) body) = t :=> typeOf body
typeOf (ReturnCode value) = F (typeOfData value)
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LetToCode _ _ body) = typeOf body
typeOf (CatchCode (Label t _) _) = t
-- typeOf (HeadCode tuple) =
--   let h :*: _ = typeOfData tuple
--    in h
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result
typeOf (ThrowCode _ _) = VoidType
typeOf (GlobalCode (Global t _)) = t

typeOfData :: Data a -> Type a
typeOfData (VariableData (Variable t _)) = t
typeOfData (ConstantData k) = Constant.typeOf k
typeOfData (ThunkData (Label t _) _) = U t
typeOfData (TailData tuple) =
  let t :*: _ = typeOfData tuple
   in t
typeOfData (PushData h t) = typeOfData h :*: typeOfData t

data Builder t a where
  CodeBuilder :: Action a -> Unique.State (Code a) -> Builder Code a
  DataBuilder :: Type a -> Unique.State (Data a) -> Builder Data a
  StackBuilder :: Action a -> Unique.State (Stack a) -> Builder Stack a

build :: Builder t a -> t a
build (CodeBuilder _ s) = Unique.run s
build (DataBuilder _ s) = Unique.run s
build (StackBuilder _ s) = Unique.run s

instance Callcc Builder where
  global g@(Global t _) = CodeBuilder t $ pure (GlobalCode g)
  returns (DataBuilder t value) = CodeBuilder (F t) $ pure ReturnCode <*> value
  letTo x@(CodeBuilder (F t) xs) f =
    let CodeBuilder bt _ = f (DataBuilder t (pure undefined))
     in CodeBuilder bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CodeBuilder _ body = f ((DataBuilder t . pure) $ VariableData v)
          body' <- body
          pure $ LetToCode x' v body'
  letBe x@(DataBuilder t xs) f =
    let CodeBuilder bt _ = f (DataBuilder t (pure undefined))
     in CodeBuilder bt $ do
          x' <- xs
          v <- pure (Variable t) <*> Unique.uniqueId
          let CodeBuilder _ body = f ((DataBuilder t . pure) $ VariableData v)
          body' <- body
          pure $ LetBeCode x' v body'
  lambda t f =
    let CodeBuilder result _ = f (DataBuilder t (pure undefined))
     in CodeBuilder (t :=> result) $ do
          v <- pure (Variable t) <*> Unique.uniqueId
          let CodeBuilder _ body = f ((DataBuilder t . pure) $ VariableData v)
          body' <- body
          pure $ LambdaCode v body'
  unit = DataBuilder UnitType $ pure UnitData
  apply (CodeBuilder (_ :=> b) f) (DataBuilder _ x) =
    CodeBuilder b $
      pure ApplyCode <*> f <*> x
  constant k = DataBuilder (Constant.typeOf k) $ pure (ConstantData k)

  thunk t f = DataBuilder (U t) $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CodeBuilder _ body = f ((StackBuilder t . pure) $ LabelStack v)
    body' <- body
    pure $ ThunkData v body'
  force (DataBuilder _ thunk) (StackBuilder _ stack) =
    CodeBuilder VoidType $
      pure ForceCode <*> thunk <*> stack

  catch t f = CodeBuilder t $ do
    v <- pure (Label t) <*> Unique.uniqueId
    let CodeBuilder _ body = f ((StackBuilder t . pure) $ LabelStack v)
    body' <- body
    pure $ CatchCode v body'
  throw (StackBuilder _ x) (CodeBuilder _ f) =
    CodeBuilder VoidType $
      pure ThrowCode <*> x <*> f

abstractCode :: (Callcc t) => Code a -> t Code a
abstractCode = abstractCode' VarMap.empty

abstractData :: (Callcc t) => Data a -> t Data a
abstractData = abstractData' VarMap.empty

abstractCode' :: (Callcc t) => VarMap (t Data) -> Code a -> t Code a
abstractCode' env (LetBeCode term binder body) = letBe (abstractData' env term) $ \x ->
  let env' = VarMap.insert binder x env
   in abstractCode' env' body
abstractCode' env (LetToCode term binder body) = letTo (abstractCode' env term) $ \x ->
  let env' = VarMap.insert binder x env
   in abstractCode' env' body
abstractCode' env (ApplyCode f x) =
  let f' = abstractCode' env f
      x' = abstractData' env x
   in apply f' x'
abstractCode' env (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
  let env' = VarMap.insert binder x env
   in abstractCode' env' body
abstractCode' env (ReturnCode val) = returns (abstractData' env val)
abstractCode' _ (GlobalCode g) = global g

abstractData' :: (Callcc t) => VarMap (t Data) -> Data x -> t Data x
abstractData' env (VariableData v@(Variable t u)) =
  case VarMap.lookup v env of
    Just x -> x
    Nothing -> error ("could not find var " ++ show u ++ " of type " ++ show t)
abstractData' _ (ConstantData k) = constant k
abstractData' _ UnitData = unit
abstractData' env (TailData tuple) = Callcc.tail (abstractData' env tuple)
abstractData' env (PushData h t) = push (abstractData' env h) (abstractData' env t)

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
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (CatchCode binder@(Label t _) body) =
    fromString "catch " <> showb binder <> fromString ": " <> showb t <> fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body))) <> fromString "\n}"
  showb (ThrowCode label body) = showb body <> fromString "\nthrow " <> showb label
  showb (ForceCode thunk stack) = fromString "! " <> showb thunk <> fromString " " <> showb stack

-- showb (HeadCode tuple) = showb tuple <> fromString "\nhead"

instance TextShow (Data a) where
  showb UnitData = fromString "."
  showb (ThunkData binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body))) <> fromString "\n}"
  showb (ConstantData k) = showb k
  showb (VariableData b) = showb b
  showb (TailData tuple) = showb tuple <> fromString "\ntail"
  showb (PushData h t) = showb h <> fromString ", " <> showb t

instance TextShow (Stack a) where
  showb (LabelStack b) = showb b

simplify :: Code a -> Code a
simplify = simpCode

simpCode :: Code a -> Code a
simpCode (LetToCode (ReturnCode value) binder body) = simpCode (LetBeCode value binder body)
simpCode (ApplyCode (LambdaCode binder body) value) = simpCode (LetBeCode value binder body)
simpCode (LambdaCode binder body) = LambdaCode binder (simpCode body)
simpCode (ApplyCode f x) = ApplyCode (simpCode f) (simpData x)
simpCode (LetBeCode thing binder body) = LetBeCode (simpData thing) binder (simpCode body)
simpCode (LetToCode act binder body) = LetToCode (simpCode act) binder (simpCode body)
simpCode (CatchCode binder body) = CatchCode binder (simpCode body)
simpCode (ThrowCode stack act) = ThrowCode stack (simpCode act)
simpCode (ForceCode th stk) = ForceCode (simpData th) stk
simpCode (ReturnCode x) = ReturnCode (simpData x)
-- simpCode (HeadCode tuple) = HeadCode (simpData tuple)
simpCode g@(GlobalCode _) = g

simpData :: Data a -> Data a
simpData UnitData = UnitData
simpData (TailData tuple) = TailData (simpData tuple)
simpData (PushData x y) = PushData (simpData x) (simpData y)
simpData (ThunkData label body) = ThunkData label (simpCode body)
simpData g@(ConstantData _) = g
simpData g@(VariableData _) = g

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (LetBeCode x binder body) = value x + code body
    code (LetToCode action binder body) = code action + code body
    code (LambdaCode binder body) = code body
    code (ApplyCode f x) = code f + value x
    code (ThrowCode _ f) = code f
    code (ForceCode x _) = value x
    code (CatchCode _ body) = code body
    code (ReturnCode x) = value x
    -- code (HeadCode tuple) = value tuple
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (PushData x y) = value x + value y
    value (TailData tuple) = value tuple
    value (ThunkData _ body) = code body
    value _ = 0

inline :: Callcc t => Code a -> t Code a
inline = inlCode LabelMap.empty VarMap.empty

newtype L t a = L (t Stack a)

inlCode :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Code a -> t Code a
inlCode lenv env (LetBeCode term binder body) =
  let term' = inlValue lenv env term
   in if Callcc.count binder body <= 1
        then inlCode lenv (VarMap.insert binder term' env) body
        else letBe term' $ \x ->
          inlCode lenv (VarMap.insert binder x env) body
inlCode lenv env (LetToCode term binder body) = letTo (inlCode lenv env term) $ \x ->
  inlCode lenv (VarMap.insert binder x env) body
inlCode lenv env (ApplyCode f x) = apply (inlCode lenv env f) (inlValue lenv env x)
inlCode lenv env (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
  inlCode lenv (VarMap.insert binder x env) body
inlCode lenv env (ReturnCode val) = returns (inlValue lenv env val)
inlCode lenv env (ThrowCode x f) = throw (inlStack lenv env x) (inlCode lenv env f)
inlCode lenv env (CatchCode binder@(Label t _) body) = catch t $ \x ->
  inlCode (LabelMap.insert binder (L x) lenv) env body
inlCode lenv env (ForceCode x f) = force (inlValue lenv env x) (inlStack lenv env f)
inlCode _ _ (GlobalCode g) = global g

inlValue :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Data x -> t Data x
inlValue _ env (VariableData variable) =
  let Just replacement = VarMap.lookup variable env
   in replacement
inlValue _ _ (ConstantData k) = constant k
inlValue lenv env (ThunkData binder@(Label t _) body) = thunk t $ \x ->
  inlCode (LabelMap.insert binder (L x) lenv) env body
inlValue lenv env (PushData x y) = push (inlValue lenv env x) (inlValue lenv env y)
-- inlValue lenv env (HeadData tuple) = Callcc.head (inlValue lenv env tuple)
inlValue lenv env (TailData tuple) = Callcc.tail (inlValue lenv env tuple)
inlValue lenv env UnitData = Callcc.unit

inlStack :: Callcc t => LabelMap (L t) -> VarMap (t Data) -> Stack x -> t Stack x
inlStack lenv _ (LabelStack l) =
  let Just (L x) = LabelMap.lookup l lenv
   in x
