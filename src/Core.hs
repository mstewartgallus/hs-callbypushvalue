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

pattern (:=>) :: forall a b. Type a -> Type b -> Type (a -> b)
pattern head :=> tail <- (ApplyType (ApplyType ((equalType fnRaw) -> Just Refl) head) tail)

pattern StackType :: Type a -> Type (Stack a)
pattern StackType x <- (ApplyType ((equalType stack) -> Just Refl) x)

pattern ThunkType :: Type a -> Type (U a)
pattern ThunkType x <- (ApplyType ((equalType thunk) -> Just Refl) x)

pattern ReturnsType :: Type a -> Type (F a)
pattern ReturnsType x <- (ApplyType ((equalType returnsType) -> Just Refl) x)
