{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (typeOf, Builder (..), Cpbv (..), Code (..), Data (..), simplify, intrinsify, inline) where

import Common
import Core
import qualified Data.Text as T
import GlobalMap (GlobalMap)
import qualified GlobalMap as GlobalMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Unique
import VarMap (VarMap)
import qualified VarMap as VarMap

typeOf :: Code a -> Type a
typeOf (GlobalCode (Global t _ _)) = t
typeOf (ForceCode thunk) =
  let ThunkType x = typeOfData thunk
   in x
typeOf (ReturnCode value) = ApplyType returnsType (typeOfData value)
typeOf (LetToCode _ _ body) = typeOf body
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (LambdaCode (Variable t _) body) = t -=> typeOf body
typeOf (ApplyCode f _) =
  let _ :=> result = typeOf f
   in result

typeOfData :: Data a -> Type a
typeOfData (VariableData (Variable t _)) = t
typeOfData (ConstantData (IntegerConstant _)) = intRaw
typeOfData (ThunkData code) = ApplyType thunk (typeOf code)

newtype Builder t a = Builder {build :: Unique.Stream -> t a}

class Cpbv t where
  global :: Global a -> t Code a
  force :: t Data (U a) -> t Code a
  returns :: t Data a -> t Code (F a)
  letTo :: t Code (F a) -> (t Data a -> t Code b) -> t Code b
  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b
  lambda :: Type a -> (t Data a -> t Code b) -> t Code (a -> b)
  apply :: t Code (a -> b) -> t Data a -> t Code b
  constant :: Constant a -> t Data a
  delay :: t Code a -> t Data (U a)

instance Cpbv Builder where
  global g = (Builder . const) $ GlobalCode g
  force thunk = Builder $ \stream ->
    ForceCode (build thunk stream)
  returns value = Builder $ \stream ->
    ReturnCode (build value stream)
  letTo x f = Builder $ \(Unique.Pick h (Unique.Split l r)) ->
    let x' = build x l
        ReturnsType t = typeOf x'
        v = Variable t h
        body = build (f ((Builder . const) $ VariableData v)) r
     in LetToCode x' v body
  letBe x f = Builder $ \(Unique.Pick h (Unique.Split l r)) ->
    let x' = build x l
        t = typeOfData x'
        v = Variable t h
        body = build (f ((Builder . const) $ VariableData v)) r
     in LetBeCode x' v body
  lambda t f = Builder $ \(Unique.Pick h stream) ->
    let v = Variable t h
        body = build (f ((Builder . const) $ VariableData v)) stream
     in LambdaCode v body
  apply f x = Builder $ \(Unique.Split l r) ->
    let f' = build f l
        x' = build x r
     in ApplyCode f' x'
  constant k = (Builder . const) $ ConstantData k
  delay code = Builder $ \stream ->
    ThunkData (build code stream)

data Code a where
  GlobalCode :: Global a -> Code a
  LambdaCode :: Variable a -> Code b -> Code (a -> b)
  ApplyCode :: Code (a -> b) -> Data a -> Code b
  ForceCode :: Data (U a) -> Code a
  ReturnCode :: Data a -> Code (F a)
  LetToCode :: Code (F a) -> Variable a -> Code b -> Code b
  LetBeCode :: Data a -> Variable a -> Code b -> Code b

data Data a where
  VariableData :: Variable a -> Data a
  ConstantData :: Constant a -> Data a
  ThunkData :: Code a -> Data (U a)

instance TextShow (Code a) where
  showb (GlobalCode g) = showb g
  showb (LambdaCode binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyCode f x) = showb x <> fromString "\n" <> showb f
  showb (ForceCode thunk) = fromString "! " <> showb thunk
  showb (ReturnCode value) = fromString "return " <> showb value
  showb (LetToCode action binder body) = showb action <> fromString " to " <> showb binder <> fromString ".\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body

instance TextShow (Data a) where
  showb (VariableData v) = showb v
  showb (ConstantData k) = showb k
  showb (ThunkData code) = fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb code))) <> fromString "\n}"

{-
Simplify Call By Push Data Inverses

So far we handle:

- force (thunk X) reduces to X
- thunk (force X) reduces to X
-}
simplify :: Code a -> Code a
simplify (ForceCode (ThunkData x)) = simplify x
simplify (ForceCode x) = ForceCode (simplifyData x)
simplify (ApplyCode (LambdaCode binder body) value) = simplify (LetBeCode value binder body)
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
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LetToCode action binder body) = code action + if AnyVariable binder == AnyVariable v then 0 else code body
    code (LambdaCode binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    code (ApplyCode f x) = code f + value x
    code (ForceCode thunk) = value thunk
    code (ReturnCode x) = value x
    code _ = 0
    value :: Data x -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (ThunkData c) = code c
    value _ = 0

inline :: Code a -> Builder Code a
inline = inline' VarMap.empty

inline' :: VarMap X -> Code a -> Builder Code a
inline' map = code
  where
    code :: Code x -> Builder Code x
    code (LetBeCode term binder body) =
      if count binder body <= 1
        then inline' (VarMap.insert binder (X (value term)) map) body
        else letBe (value term) $ \x ->
          inline' (VarMap.insert binder (X x) map) body
    code (LetToCode term binder body) = letTo (code term) $ \x ->
      inline' (VarMap.insert binder (X x) map) body
    code (ApplyCode f x) = apply (code f) (value x)
    code (LambdaCode binder@(Variable t _) body) = lambda t $ \x ->
      inline' (VarMap.insert binder (X x) map) body
    code (ForceCode th) = force (value th)
    code (ReturnCode val) = returns (value val)
    code (GlobalCode g) = global g
    value :: Data x -> Builder Data x
    value (VariableData variable) =
      let Just (X replacement) = VarMap.lookup variable map
       in replacement
    value (ThunkData c) = delay (code c)
    value (ConstantData k) = constant k

-- Fixme... use a different file for this?
intrinsify :: Code a -> Builder Code a
intrinsify code = intrins VarMap.empty code

newtype X a = X (Builder Data a)

intrins :: VarMap X -> Code a -> Builder Code a
intrins env (GlobalCode g) = case GlobalMap.lookup g intrinsics of
  Nothing -> global g
  Just (Intrinsic intrinsic) -> intrinsic
intrins env (ApplyCode f x) = apply (intrins env f) (intrinsData env x)
intrins env (ForceCode x) = force (intrinsData env x)
intrins env (ReturnCode x) = returns (intrinsData env x)
intrins env (LambdaCode binder@(Variable t _) body) = lambda t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in intrins env' body
intrins env (LetBeCode value binder body) = letBe (intrinsData env value) $ \value ->
  let env' = VarMap.insert binder (X value) env
   in intrins env' body
intrins env (LetToCode action binder body) = letTo (intrins env action) $ \value ->
  let env' = VarMap.insert binder (X value) env
   in intrins env' body

intrinsData :: VarMap X -> Data a -> Builder Data a
intrinsData env (ThunkData code) = delay (intrins env code)
intrinsData env (VariableData binder) =
  let Just (X x) = VarMap.lookup binder env
   in x
intrinsData env (ConstantData x) = constant x

newtype Intrinsic a = Intrinsic (Builder Code a)

intrinsics :: GlobalMap Intrinsic
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus (Intrinsic plusIntrinsic)
    ]

plusIntrinsic :: Builder Code (F Integer :-> F Integer :-> F Integer)
plusIntrinsic =
  lambda (ApplyType thunk int) $ \x' ->
    lambda (ApplyType thunk int) $ \y' ->
      letTo (force x') $ \x'' ->
        letTo (force y') $ \y'' ->
          apply (apply (global strictPlus) x'') y''
