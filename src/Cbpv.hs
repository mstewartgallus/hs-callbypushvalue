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
  CB :: (forall s. Unique.Stream s -> (Action a, Code a)) -> Builder Code a
  DB :: (forall s. Unique.Stream s -> (Type a, Data a)) -> Builder Data a

build :: Builder t a -> t a
build (CB s) = snd (Unique.withStream s)
build (DB s) = snd (Unique.withStream s)

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
  global g@(Global t _) = CB $ \_ -> (t, GlobalCode g)
  unit = DB $ \_ -> (UnitType, UnitData)
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantData k)

  force (DB thunk) = CB $ \s ->
    let (U t, thunk') = thunk s
     in (t, ForceCode thunk')
  thunk (CB code) = DB $ \s ->
    let (t, code') = code s
     in (U t, ThunkData code')

  returns (DB value) = CB $ \s ->
    let (t, value') = value s
     in (F t, ReturnCode value')

  letTo (CB x) f = CB $ \(Unique.Stream newId xs fs) ->
    let (F tx, vx) = x xs
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
             in (t :=> result, LambdaCode binder body)
  apply (CB f) (DB x) = CB $ \(Unique.Stream _ fs xs) ->
    let (_ :=> b, vf) = f fs
        (_, vx) = x xs
     in (b, ApplyCode vf vx)

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

inline :: Cbpv t => Code a -> t Code a
inline = inlCode VarMap.empty

inlCode :: Cbpv t => VarMap (t Data) -> Code a -> t Code a
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

inlValue :: Cbpv t => VarMap (t Data) -> Data x -> t Data x
inlValue env x = case x of
  VariableData variable ->
    let Just replacement = VarMap.lookup variable env
     in replacement
  ThunkData c -> thunk (inlCode env c)
  ConstantData k -> constant k
  UnitData -> unit
  TailData tuple -> Cbpv.tail (inlValue env tuple)
  PushData h t -> push (inlValue env h) (inlValue env t)

abstractCode :: (Cbpv t) => Code a -> t Code a
abstractCode = abstractCode' VarMap.empty

abstractData :: (Cbpv t) => Data a -> t Data a
abstractData = abstractData' VarMap.empty

abstractCode' :: (Cbpv t) => VarMap (t Data) -> Code a -> t Code a
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

abstractData' :: (Cbpv t) => VarMap (t Data) -> Data x -> t Data x
abstractData' env x = case x of
  VariableData v@(Variable t u) -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error ("could not find var " ++ show u ++ " of type " ++ show t)
  ThunkData c -> thunk (abstractCode' env c)
  ConstantData k -> constant k
  UnitData -> unit
  TailData tuple -> Cbpv.tail (abstractData' env tuple)
  PushData h t -> push (abstractData' env h) (abstractData' env t)

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
