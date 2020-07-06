{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Core
  ( fn,
    thunk,
    stack,
    pattern (:=>),
    (-=>),
    (-#->),
    pattern ReturnsType,
    pattern StackType,
    pattern ThunkType,
    returnsType,
    int,
    intRaw,
    plus,
    strictPlus,
  )
where

import Common
import qualified Data.Text as T
import Data.Typeable
import Global
import Name
import Unsafe.Coerce

{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}
fn :: Type (V a (V b (a :-> b)))
fn = LambdaType $ \x ->
  LambdaType $ \y ->
    NominalType $ TypeApp (TypeApp fn' x) y

fn' :: TypeName (V a (V b (a :-> b)))
fn' = TypeName $ Name (T.pack "core") (T.pack "fn")

-- fixme implement in terms of stack...
thunk :: Type (V a (U a))
thunk = LambdaType $ \x ->
  NominalType $ TypeApp thunk' x

thunk' :: TypeName (V a (U a))
thunk' = TypeName $ Name (T.pack "core") (T.pack "U")

fnRaw' :: TypeName (V a (V b (a -> b)))
fnRaw' = TypeName $ Name (T.pack "core") (T.pack "fnRaw")

fnRaw :: Type (V a (V b (a -> b)))
fnRaw = LambdaType $ \x ->
  LambdaType $ \y ->
    NominalType $ TypeApp (TypeApp fnRaw' x) y

returnsType :: Type (V a (F a))
returnsType = LambdaType $ \x ->
  NominalType $ TypeApp returnsType' x

returnsType' :: TypeName (V a (F a))
returnsType' = TypeName $ Name (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = applyType returnsType intRaw

intRaw :: Type Integer
intRaw = NominalType $ TypeName $ Name (T.pack "core") (T.pack "int")

stack :: Type (V a (Stack a))
stack = LambdaType $ \x ->
  NominalType $ TypeApp stack' x

stack' :: TypeName (V a (Stack a))
stack' = TypeName $ Name (T.pack "core") (T.pack "stack")

plus :: Global (F Integer :-> F Integer :-> F Integer)
plus = Global (u int -=> u int -=> int) $ Name (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global (intRaw -=> intRaw -=> int) $ Name (T.pack "core") (T.pack "+!")

u :: Type a -> Type (U a)
u x = applyType thunk x

infixr 9 -=>

(-=>) :: Type a -> Type b -> Type (a -> b)
a -=> b = applyType (applyType fnRaw a) b

infixr 9 -#->

(-#->) :: Type a -> Type b -> Type (a :-> b)
a -#-> b = applyType (applyType fnRaw (applyType thunk a)) b

decompose :: Type (a -> b) -> (Type a, Type b)
decompose (NominalType (TypeApp (TypeApp f x) y)) =
  let Just Refl = equalName f fnRaw'
   in -- fixme... wtf?
      (unsafeCoerce x, unsafeCoerce y)

pattern head :=> tail <- (decompose -> (head, tail))

getstacktype :: Type (Stack a) -> Type a
getstacktype (NominalType (TypeApp f x)) =
  let Just Refl = equalName f stack'
   in -- fixme... wtf?
      unsafeCoerce x

getthunktype :: Type (U a) -> Type a
getthunktype (NominalType (TypeApp f x)) =
  let Just Refl = equalName f thunk'
   in -- fixme... wtf?
      unsafeCoerce x

getreturntype :: Type (F a) -> Type a
getreturntype (NominalType (TypeApp f x)) =
  let Just Refl = equalName f returnsType'
   in -- fixme... wtf?
      unsafeCoerce x

pattern StackType x <- (getstacktype -> x)

pattern ThunkType x <- (getthunktype -> x)

pattern ReturnsType x <- (getreturntype -> x)
