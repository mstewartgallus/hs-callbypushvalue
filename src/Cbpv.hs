{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (abstractCode, build, Builder, Cbpv (..), Code (..), Data (..), simplify, intrinsify, inline) where

import Basic
import Common
import Const
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Explicit
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

class (Basic t, Const t, Explicit t) => Cbpv t where
  thunk :: AlgRep t a -> SetRep t (U a)
  force :: SetRep t (U a) -> AlgRep t a

  push :: SetRep t a -> SetRep t b -> SetRep t (a :*: b)

  -- fixme... use an indirect style for this...
  tail :: SetRep t (a :*: b) -> SetRep t a
  head :: SetRep t (a :*: b) -> SetRep t b

data Builder

build :: AlgRep Builder a -> Code a
build (CB s) = snd (Unique.withStream s)

instance Basic Builder where
  newtype AlgRep Builder (a :: Alg) = CB (forall s. Unique.Stream s -> (SAlg a, Code a))
  global g@(Global t _) = CB $ \_ -> (t, GlobalCode g)

instance Const Builder where
  newtype SetRep Builder (a :: Set) = DB (forall s. Unique.Stream s -> (SSet a, Data a))
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantData k)
  unit = DB $ \_ -> (SUnit, UnitData)

instance Explicit Builder where
  returns (DB value) = CB $ \s ->
    let (t, value') = value s
     in (SF t, ReturnCode value')

  letTo (CB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (SF tx, vx) = x xs
        binder = Variable tx newId
     in case f (DB $ \_ -> (tx, VariableData binder)) of
          CB b ->
            let (result, body) = b fs
             in (result, LetToCode vx binder body)
  letBe (DB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (tx, vx) = x xs
        binder = Variable tx newId
     in case f (DB $ \_ -> (tx, VariableData binder)) of
          CB b ->
            let (result, body) = b fs
             in (result, LetBeCode vx binder body)

  lambda t f = CB $ \(Unique.Stream newId xs fs) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableData binder)) of
          CB b ->
            let (result, body) = b fs
             in (t `SFn` result, LambdaCode binder body)
  apply (CB f) (DB x) = CB $ \(Unique.Stream _ fs xs) ->
    let (_ `SFn` b, vf) = f fs
        (_, vx) = x xs
     in (b, ApplyCode vf vx)

instance Cbpv Builder where
  force (DB thunk) = CB $ \s ->
    let (SU t, thunk') = thunk s
     in (t, ForceCode thunk')
  thunk (CB code) = DB $ \s ->
    let (t, code') = code s
     in (SU t, ThunkData code')

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
    VS b -> Unique.withStream b

data View

instance Basic View where
  newtype AlgRep View a = V (forall s. Unique.Stream s -> TextShow.Builder)
  global g = V $ \_ -> showb g

instance Const View where
  newtype SetRep View a = VS (forall s. Unique.Stream s -> TextShow.Builder)
  constant k = VS $ \_ -> showb k
  unit = VS $ \_ -> fromString "."

instance Explicit View where
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

instance Cbpv View where
  thunk (V code) = VS $ \s -> fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> code s))) <> fromString "\n}"
  force (VS thunk) = V $ \s -> fromString "! " <> thunk s

{-
Simplify Call By Push Data Inverses

So far we handle:

- force (thunk X) reduces to X
- thunk (force X) reduces to X
-}
simplify :: Code a -> Code a
simplify code = case code of
  LetToCode (ReturnCode value) binder body -> simplify (LetBeCode value binder body)
  ApplyCode (LambdaCode binder body) value -> simplify (LetBeCode value binder body)
  ForceCode (ThunkData x) -> simplify x
  ForceCode x -> ForceCode (simplifyData x)
  LambdaCode binder body -> LambdaCode binder (simplify body)
  ApplyCode f x -> ApplyCode (simplify f) (simplifyData x)
  ReturnCode value -> ReturnCode (simplifyData value)
  LetBeCode value binder body -> LetBeCode (simplifyData value) binder (simplify body)
  LetToCode action binder body -> LetToCode (simplify action) binder (simplify body)
  x -> x

simplifyData :: Data a -> Data a
simplifyData x = case x of
  ThunkData (ForceCode x) -> simplifyData x
  ThunkData x -> ThunkData (simplify x)
  x -> x

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code c = case c of
      LetBeCode x binder body -> value x + code body
      LetToCode action binder body -> code action + code body
      LambdaCode binder body -> code body
      ApplyCode f x -> code f + value x
      ForceCode thunk -> value thunk
      ReturnCode x -> value x
      _ -> 0
    value :: Data x -> Int
    value x = case x of
      PushData h t -> value h + value t
      TailData tuple -> value tuple
      VariableData binder -> if AnyVariable v == AnyVariable binder then 1 else 0
      ThunkData c -> code c
      _ -> 0

inline :: Cbpv t => Code a -> AlgRep t a
inline = inlCode VarMap.empty

inlCode :: Cbpv t => VarMap (SetRep t) -> Code a -> AlgRep t a
inlCode env code = case code of
  LetBeCode term binder body ->
    let term' = inlValue env term
     in if count binder body <= 1
          then inlCode (VarMap.insert binder term' env) body
          else letBe term' $ \x ->
            inlCode (VarMap.insert binder x env) body
  LetToCode term binder body -> letTo (inlCode env term) $ \x ->
    inlCode (VarMap.insert binder x env) body
  ApplyCode f x -> apply (inlCode env f) (inlValue env x)
  LambdaCode binder@(Variable t _) body -> lambda t $ \x ->
    inlCode (VarMap.insert binder x env) body
  ForceCode th -> force (inlValue env th)
  ReturnCode val -> returns (inlValue env val)
  GlobalCode g -> global g

inlValue :: Cbpv t => VarMap (SetRep t) -> Data x -> SetRep t x
inlValue env x = case x of
  VariableData variable ->
    let Just v = VarMap.lookup variable env
     in v
  ThunkData c -> thunk (inlCode env c)
  ConstantData k -> constant k
  UnitData -> unit
  TailData tuple -> Cbpv.tail (inlValue env tuple)
  PushData h t -> push (inlValue env h) (inlValue env t)

abstractCode :: Cbpv t => Code a -> AlgRep t a
abstractCode = abstractCode' VarMap.empty

abstractData :: Cbpv t => Data a -> SetRep t a
abstractData = abstractData' VarMap.empty

abstractCode' :: Cbpv t => VarMap (SetRep t) -> Code a -> AlgRep t a
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
  ForceCode th -> force (abstractData' env th)
  ReturnCode val -> returns (abstractData' env val)
  GlobalCode g -> global g

abstractData' :: Cbpv t => VarMap (SetRep t) -> Data x -> SetRep t x
abstractData' env x = case x of
  VariableData v@(Variable t u) -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error ("could not find var " ++ show u)
  ThunkData c -> thunk (abstractCode' env c)
  ConstantData k -> constant k
  UnitData -> unit
  TailData tuple -> Cbpv.tail (abstractData' env tuple)
  PushData h t -> push (abstractData' env h) (abstractData' env t)

-- Fixme... use a different file for this?
intrinsify :: Cbpv t => Code a -> AlgRep t a
intrinsify code = case abstractCode code of
  I x -> abstractCode (build x)

data Intrinsify t

instance Cbpv t => Basic (Intrinsify t) where
  newtype AlgRep (Intrinsify t) a = I (AlgRep t a)
  global g = I $ case GlobalMap.lookup g intrinsics of
    Nothing -> global g
    Just intrinsic -> intrinsic

instance Const t => Const (Intrinsify t) where
  newtype SetRep (Intrinsify t) a = IS (SetRep t a)
  constant k = IS (constant k)
  unit = IS unit

instance Cbpv t => Explicit (Intrinsify t) where
  returns (IS x) = I (returns x)

  letTo (I x) f = I $ letTo x $ \x' ->
    let I body = f (IS x')
     in body
  letBe (IS x) f = I $ letBe x $ \x' ->
    let I body = f (IS x')
     in body

  lambda t f = I $ lambda t $ \x ->
    let I body = f (IS x)
     in body
  apply (I f) (IS x) = I (apply f x)

instance Cbpv t => Cbpv (Intrinsify t) where
  thunk (I x) = IS (thunk x)
  force (IS x) = I (force x)

intrinsics :: Cbpv t => GlobalMap (AlgRep t)
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus plusIntrinsic
    ]

plusIntrinsic :: Cbpv t => AlgRep t (F U64 :-> F U64 :-> F U64)
plusIntrinsic = lambda (SU (SF SU64)) $ \x' ->
  lambda (SU (SF SU64)) $ \y' ->
    letTo (force x') $ \x'' ->
      letTo (force y') $ \y'' ->
        apply (apply (global strictPlus) x'') y''
