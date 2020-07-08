{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Core
  ( pattern (:=>),
    pattern F,
    pattern StackType,
    pattern U,
    pattern IntType,
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
plus = Global (U int :=> U int :=> int) $ Name (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global (intRaw :=> intRaw :=> int) $ Name (T.pack "core") (T.pack "+!")

infixr 9 :=>

pattern (:=>) :: Type a -> Type b -> Type (a -> b)
pattern head :=> tail <-
  (ApplyType (ApplyType ((equalType fnRaw) -> Just Refl) head) tail)
  where
    a :=> b = ApplyType (ApplyType fnRaw a) b

pattern IntType :: Type Integer
pattern IntType <-
  ((equalType intRaw) -> Just Refl)
  where
    IntType = intRaw

pattern StackType :: Type a -> Type (Stack a)
pattern StackType x <-
  (ApplyType ((equalType stack) -> Just Refl) x)
  where
    StackType x = ApplyType stack x

pattern U :: Type a -> Type (U a)
pattern U x <-
  (ApplyType ((equalType thunk) -> Just Refl) x)
  where
    U x = ApplyType thunk x

pattern F :: Type a -> Type (F a)
pattern F x <-
  (ApplyType ((equalType returnsType) -> Just Refl) x)
  where
    F x = ApplyType returnsType x
