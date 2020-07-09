{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Core
  ( pattern StackType,
    pattern U,
    pattern IntType,
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

int :: Type Integer
int = NominalType TypeKind (Name (T.pack "core") (T.pack "int"))

stack :: Type (V a (Stack a))
stack = NominalType (TypeKind `FunKind` TypeKind) stack'

stack' :: Name
stack' = Name (T.pack "core") (T.pack "stack")

plus :: Global (U (F Integer :-> F Integer :-> F Integer))
plus = Global (U (U (F int) :=> U (F int) :=> F int)) $ Name (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (U (Integer :=> Integer :=> F Integer))
strictPlus = Global (U (int :=> int :=> F int)) $ Name (T.pack "core") (T.pack "+!")

pattern IntType :: Type Integer
pattern IntType <-
  ((equalType int) -> Just Refl)
  where
    IntType = int

pattern StackType :: (b ~ Stack a) => Action a -> Type b
pattern StackType x <-
  (ApplyAction ((equalType stack) -> Just Refl) x)
  where
    StackType x = ApplyAction stack x

pattern U :: (b ~ U a) => Action a -> Type b
pattern U x <-
  (ApplyAction ((equalType thunk) -> Just Refl) x)
  where
    U x = ApplyAction thunk x
