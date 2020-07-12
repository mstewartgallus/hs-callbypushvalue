{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Core
  ( pattern U,
    pattern (:*:),
    pattern IntType,
    pattern UnitType,
    minus,
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

tuple :: Type (V a (V b (a :*: b)))
tuple = NominalType (TypeKind `FunKind` (TypeKind `FunKind` TypeKind)) $ Name (T.pack "core") (T.pack "T")

thunk' :: Name
thunk' = Name (T.pack "core") (T.pack "U")

int :: Type Integer
int = NominalType TypeKind (Name (T.pack "core") (T.pack "int"))

unit :: Type Unit
unit = NominalType TypeKind (Name (T.pack "core") (T.pack "unit"))

plus :: Global (F Integer :-> F Integer :-> F Integer)
plus = Global (U (F int) :=> U (F int) :=> F int) $ Name (T.pack "core") (T.pack "+")

minus :: Global (F Integer :-> F Integer :-> F Integer)
minus = Global (U (F int) :=> U (F int) :=> F int) $ Name (T.pack "core") (T.pack "-")

-- fixme...
strictPlus :: Global (Integer :=> Integer :=> F Integer)
strictPlus = Global (int :=> int :=> F int) $ Name (T.pack "core") (T.pack "+!")

pattern IntType :: Type Integer
pattern IntType <-
  ((equalType int) -> Just Refl)
  where
    IntType = int

pattern UnitType :: Type Unit
pattern UnitType <-
  ((equalType unit) -> Just Refl)
  where
    UnitType = unit

pattern U :: (b ~ U a) => Action a -> Type b
pattern U x <-
  (ApplyAction ((equalType thunk) -> Just Refl) x)
  where
    U x = ApplyAction thunk x

infixr 0 :*:

pattern (:*:) :: (c ~ (a :*: b)) => Type a -> Type b -> Type c
pattern x :*: y <-
  (ApplyType (ApplyType ((equalType tuple) -> Just Refl) x) y)
  where
    x :*: y = ApplyType (ApplyType tuple x) y
