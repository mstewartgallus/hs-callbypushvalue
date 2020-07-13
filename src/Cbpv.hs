{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (abstractCode, build, Builder, Cbpv (..), Code (..), Data (..), simplify, intrinsify, inline) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Global
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import qualified TextShow (Builder)
import Type
import Unique
import VarMap (VarMap)
import qualified VarMap as VarMap
import Variable

data Builder t a where
  CodeBuilder :: Action a -> Unique.State (Code a) -> Builder Code a
  DataBuilder :: Type a -> Unique.State (Data a) -> Builder Data a

build :: Builder t a -> t a
build (CodeBuilder _ s) = Unique.run s
build (DataBuilder _ s) = Unique.run s

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
  thunk :: t Code a -> t Data (U a)

instance Cbpv Builder where
  global g@(Global t _) = CodeBuilder t $ pure (GlobalCode g)
  force (DataBuilder (U t) thunk) = CodeBuilder t $ pure ForceCode <*> thunk
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
  thunk (CodeBuilder t code) =
    DataBuilder (U t) $
      pure ThunkData <*> code

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
  showb term = case abstractCode term of
    V b -> Unique.withStream b

instance TextShow (Data a) where
  showb term = case abstractData term of
    V b -> Unique.withStream b

newtype View (tag :: * -> *) a = V (forall s. Unique.Stream s -> TextShow.Builder)

instance Cbpv View where
  global g = V $ \_ -> showb g
  unit = V $ \_ -> fromString "."
  constant k = V $ \_ -> showb k

  returns (V value) = V $ \s -> fromString "return " <> value s

  letTo (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in x xs <> fromString " to " <> binder <> fromString ".\n" <> y ys
  letBe (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = V $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        V body = f (V $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  apply (V f) (V x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n" <> f fs

  thunk (V code) = V $ \s -> fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> code s))) <> fromString "\n}"
  force (V thunk) = V $ \s -> fromString "! " <> thunk s

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
inlValue env (ThunkData c) = thunk (inlCode env c)
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
abstractData' env (ThunkData c) = thunk (abstractCode' env c)
abstractData' _ (ConstantData k) = constant k
abstractData' _ UnitData = unit
abstractData' env (TailData tuple) = Cbpv.tail (abstractData' env tuple)
abstractData' env (PushData h t) = push (abstractData' env h) (abstractData' env t)

-- Fixme... use a different file for this?
intrinsify :: Cbpv t => Code a -> t Code a
intrinsify code = case abstractCode code of
  I x -> x

newtype Intrinsify t (tag :: * -> *) a = I (t tag a)

instance Cbpv t => Cbpv (Intrinsify t) where
  global g = I $ case GlobalMap.lookup g intrinsics of
    Nothing -> global g
    Just (Intrinsic intrinsic) -> intrinsic

  unit = I unit

  thunk (I x) = I (thunk x)
  force (I x) = I (force x)

  returns (I x) = I (returns x)

  letTo (I x) f = I $ letTo x $ \x' ->
    let I body = f (I x')
     in body
  letBe (I x) f = I $ letBe x $ \x' ->
    let I body = f (I x')
     in body

  lambda t f = I $ lambda t $ \x ->
    let I body = f (I x)
     in body
  apply (I f) (I x) = I (apply f x)

  constant k = I (constant k)

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
