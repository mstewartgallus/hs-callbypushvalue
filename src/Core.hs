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
import Kind
import Name
import Type
import Unsafe.Coerce

{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}
fn :: Type (V a (V b (a :-> b)))
fn = NominalType (TypeKind `FunKind` (TypeKind `FunKind` TypeKind)) fn'

fn' :: Name
fn' = Name (T.pack "core") (T.pack "fn")

-- fixme implement in terms of stack...
thunk :: Type (V a (U a))
thunk = NominalType (TypeKind `FunKind` TypeKind) thunk'

thunk' :: Name
thunk' = Name (T.pack "core") (T.pack "U")

fnRaw' :: Name
fnRaw' = Name (T.pack "core") (T.pack "fnRaw")

fnRaw :: Type (V a (V b (a -> b)))
fnRaw = NominalType (TypeKind `FunKind` (TypeKind `FunKind` TypeKind)) fnRaw'

returnsType :: Type (V a (F a))
returnsType = NominalType (TypeKind `FunKind` TypeKind) returnsType'

returnsType' :: Name
returnsType' = Name (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = applyType returnsType intRaw

intRaw :: Type Integer
intRaw = NominalType TypeKind (Name (T.pack "core") (T.pack "int"))

stack :: Type (V a (Stack a))
stack = NominalType (TypeKind `FunKind` TypeKind) stack'

stack' :: Name
stack' = Name (T.pack "core") (T.pack "stack")

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
decompose (ApplyType (ApplyType f x) y) =
  let Just Refl = equalType f fnRaw
   in -- fixme... wtf?
      (unsafeCoerce x, unsafeCoerce y)

pattern head :=> tail <- (decompose -> (head, tail))

getstacktype :: Type (Stack a) -> Type a
getstacktype (ApplyType f x) =
  let Just Refl = equalType f stack
   in -- fixme... wtf?
      unsafeCoerce x

getthunktype :: Type (U a) -> Type a
getthunktype (ApplyType f x) =
  let Just Refl = equalType f thunk
   in -- fixme... wtf?
      unsafeCoerce x

getreturntype :: Type (F a) -> Type a
getreturntype (ApplyType f x) =
  let Just Refl = equalType f returnsType
   in -- fixme... wtf?
      unsafeCoerce x

pattern StackType x <- (getstacktype -> x)

pattern ThunkType x <- (getthunktype -> x)

pattern ReturnsType x <- (getreturntype -> x)
