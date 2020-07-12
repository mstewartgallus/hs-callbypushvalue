{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (typeOf, typeOfData, build, Builder, Cbpv (..), Code (..), Data (..), simplify, intrinsify, inline) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Global
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Type
import Unique
import VarMap (VarMap)
import qualified VarMap as VarMap
import Variable

-- cannot be implemented with abstract because this is used when building stuff up.
typeOf :: Code a -> Action a
typeOf (ForceCode thunk) =
  let U x = typeOfData thunk
   in x
typeOf (ReturnCode value) = F (typeOfData value)
typeOf (LetToCode _ _ body) = typeOf body
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LambdaCode (Variable t _) body) = t :=> typeOf body
typeOf (GlobalCode (Global t _)) = t
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result

typeOfData :: Data a -> Type a
typeOfData UnitData = UnitType
typeOfData (VariableData (Variable t _)) = t
typeOfData (ConstantData k) = Constant.typeOf k
typeOfData (ThunkData code) = U (typeOf code)
typeOfData (PushData x y) = typeOfData x :*: typeOfData y
typeOfData (TailData tuple) =
  let t :*: _ = typeOfData tuple
   in t

newtype Builder t a = Builder {builder :: Unique.State (t a)}

build :: Builder t a -> t a
build (Builder s) = Unique.run s

class Cbpv t where
  global :: Global a -> t Code a
  force :: t Data (U a) -> t Code a
  returns :: t Data a -> t Code (F a)
  letTo :: t Code (F a) -> (t Data a -> t Code b) -> t Code b
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b

  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a :=> b)
  apply :: t Code (a :=> b) -> t Data a -> t Code b

  push :: t Data a -> t Data b -> t Data (a :*: b)

  -- fixme... use an indirect style for this...
  tail :: t Data (a :*: b) -> t Data a
  head :: t Data (a :*: b) -> t Data b

  unit :: t Data Unit

  constant :: Constant a -> t Data a
  delay :: t Code a -> t Data (U a)

instance Cbpv Builder where
  global g = (Builder . pure) $ GlobalCode g
  force thunk =
    Builder $
      pure ForceCode <*> builder thunk
  returns value =
    Builder $
      pure ReturnCode <*> builder value
  letTo x f = Builder $ do
    x' <- builder x
    let F t = typeOf x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ LetToCode x' v body
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOfData x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ LetBeCode x' v body
  lambda t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ LambdaCode v body
  unit = Builder $ pure $ UnitData
  push h t =
    Builder $
      pure PushData <*> builder h <*> builder t

  -- head tuple =
  --   Builder $
  --     pure HeadCode <*> builder tuple
  tail tuple =
    Builder $
      pure TailData <*> builder tuple
  apply f x =
    Builder $
      pure ApplyCode <*> builder f <*> builder x
  constant k = (Builder . pure) $ ConstantData k
  delay code =
    Builder $
      pure ThunkData <*> builder code

data Code a where
  LambdaCode :: Variable a -> Code b -> Code (a :=> b)
  ApplyCode :: Code (a :=> b) -> Data a -> Code b
  ForceCode :: Data (U a) -> Code a
  ReturnCode :: Data a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Data a -> Variable a -> Code b -> Code b
  GlobalCode :: Global a -> Code a

data Data a where
  VariableData :: Variable a -> Data a
  ConstantData :: Constant a -> Data a
  UnitData :: Data Unit
  ThunkData :: Code a -> Data (U a)
  PushData :: Data a -> Data b -> Data (a :*: b)
  HeadData :: Data (a :*: b) -> Data b
  TailData :: Data (a :*: b) -> Data a

instance TextShow (Code a) where
  showb (LambdaCode binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ForceCode thunk) = fromString "! " <> showb thunk
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (GlobalCode g) = showb g

instance TextShow (Data a) where
  showb (VariableData v) = showb v
  showb (ConstantData k) = showb k
  showb UnitData = fromString "."
  showb (ThunkData code) = fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb code))) <> fromString "\n}"
  showb (PushData h t) = showb h <> fromString ", " <> showb t
  showb (TailData tuple) = showb tuple <> fromString "\ntail"

{-
Simplify Call By Push Data Inverses

So far we handle:

- force (thunk X) reduces to X
- thunk (force X) reduces to X
-}
simplify :: Code a -> Code a
simplify (LetToCode (ReturnCode value) binder body) = simplify (LetBeCode value binder body)
simplify (ApplyCode (LambdaCode binder body) value) = simplify (LetBeCode value binder body)
simplify (ForceCode (ThunkData x)) = simplify x
simplify (ForceCode x) = ForceCode (simplifyData x)
simplify (LambdaCode binder body) =
  let body' = simplify body
   in LambdaCode binder body'
simplify (ApplyCode f x) = ApplyCode (simplify f) (simplifyData x)
simplify (ReturnCode value) = ReturnCode (simplifyData value)
simplify (LetBeCode value binder body) = LetBeCode (simplifyData value) binder (simplify body)
simplify (LetToCode action binder body) = LetToCode (simplify action) binder (simplify body)
simplify x = x

simplifyData :: Data a -> Data a
simplifyData (ThunkData (ForceCode x)) = simplifyData x
simplifyData (ThunkData x) = ThunkData (simplify x)
simplifyData x = x

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (LetBeCode x binder body) = value x + code body
    code (LetToCode action binder body) = code action + code body
    code (LambdaCode binder body) = code body
    code (ApplyCode f x) = code f + value x
    code (ForceCode thunk) = value thunk
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (PushData h t) = value h + value t
    value (TailData tuple) = value tuple
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (ThunkData c) = code c
    value _ = 0

inline :: Cbpv t => Code a -> t Code a
inline = inlCode VarMap.empty

inlCode :: Cbpv t => VarMap (t Data) -> Code a -> t Code a
-- inlCode env (HeadCode tuple) = Cbpv.head (inlValue env tuple)
inlCode env (LetBeCode term binder body) =
  let term' = inlValue env term
   in if count binder body <= 1
        then inlCode (VarMap.insert binder term' env) body
        else letBe term' $ \x ->
          inlCode (VarMap.insert binder x env) body
inlCode env (LetToCode term binder body) = letTo (inlCode env term) $ \x ->
  inlCode (VarMap.insert binder x env) body
inlCode env (ApplyCode f x) = apply (inlCode env f) (inlValue env x)
inlCode env (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
  inlCode (VarMap.insert binder x env) body
inlCode env (ForceCode th) = force (inlValue env th)
inlCode env (ReturnCode val) = returns (inlValue env val)
inlCode _ (GlobalCode g) = global g

inlValue :: Cbpv t => VarMap (t Data) -> Data x -> t Data x
inlValue env (VariableData variable) =
  let Just replacement = VarMap.lookup variable env
   in replacement
inlValue env (ThunkData c) = delay (inlCode env c)
inlValue _ (ConstantData k) = constant k
inlValue _ UnitData = unit
inlValue env (TailData tuple) = Cbpv.tail (inlValue env tuple)
inlValue env (PushData h t) = push (inlValue env h) (inlValue env t)

abstractCode :: (Cbpv t) => Code a -> t Code a
abstractCode = abstractCode' VarMap.empty

abstractData :: (Cbpv t) => Data a -> t Data a
abstractData = abstractData' VarMap.empty

abstractCode' :: (Cbpv t) => VarMap (t Data) -> Code a -> t Code a
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
abstractCode' env (ForceCode th) = force (abstractData' env th)
abstractCode' env (ReturnCode val) = returns (abstractData' env val)
abstractCode' _ (GlobalCode g) = global g

abstractData' :: (Cbpv t) => VarMap (t Data) -> Data x -> t Data x
abstractData' env (VariableData v@(Variable t u)) =
  case VarMap.lookup v env of
    Just x -> x
    Nothing -> error ("could not find var " ++ show u ++ " of type " ++ show t)
abstractData' env (ThunkData c) = delay (abstractCode' env c)
abstractData' _ (ConstantData k) = constant k
abstractData' _ UnitData = unit
abstractData' env (TailData tuple) = Cbpv.tail (abstractData' env tuple)
abstractData' env (PushData h t) = push (abstractData' env h) (abstractData' env t)

-- Fixme... use a different file for this?
intrinsify :: Cbpv t => Code a -> t Code a
intrinsify code = case abstractCode code of
  Intrinsify x -> x

newtype Intrinsify t (tag :: * -> *) a = Intrinsify (t tag a)

instance Cbpv t => Cbpv (Intrinsify t) where
  global g = Intrinsify $ case GlobalMap.lookup g intrinsics of
    Nothing -> global g
    Just (Intrinsic intrinsic) -> intrinsic

  unit = Intrinsify unit

  delay (Intrinsify x) = Intrinsify (delay x)
  force (Intrinsify x) = Intrinsify (force x)

  returns (Intrinsify x) = Intrinsify (returns x)

  letTo (Intrinsify x) f = Intrinsify $ letTo x $ \x' ->
    let Intrinsify body = f (Intrinsify x')
     in body
  letBe (Intrinsify x) f = Intrinsify $ letBe x $ \x' ->
    let Intrinsify body = f (Intrinsify x')
     in body

  lambda t f = Intrinsify $ lambda t $ \x ->
    let Intrinsify body = f (Intrinsify x)
     in body
  apply (Intrinsify f) (Intrinsify x) = Intrinsify (apply f x)

  constant k = Intrinsify (constant k)

newtype Intrinsic t a = Intrinsic (t Code a)

intrinsics :: Cbpv t => GlobalMap (Intrinsic t)
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus (Intrinsic plusIntrinsic)
    ]

plusIntrinsic :: Cbpv t => t Code (F Integer :-> F Integer :-> F Integer)
plusIntrinsic = lambda (U (F IntType)) $
  \x' ->
    lambda (U (F IntType)) $ \y' ->
      letTo (force x') $ \x'' ->
        letTo (force y') $ \y'' ->
          apply (apply (global strictPlus) x'') y''
