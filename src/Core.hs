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
import Unsafe.Coerce

{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}
fn :: Type (V a (V b (a :-> b)))
fn = NominalType $ TypeName (T.pack "core") (T.pack "fn")

-- fixme implement in terms of stack...
thunk :: Type (V a (U a))
thunk = NominalType $ TypeName (T.pack "core") (T.pack "U")

fnRaw :: Type (V a (V b (a -> b)))
fnRaw = NominalType $ TypeName (T.pack "core") (T.pack "fnRaw")

returnsType :: Type (V a (F a))
returnsType = NominalType $ TypeName (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = ApplyType returnsType intRaw

intRaw :: Type Integer
intRaw = NominalType $ TypeName (T.pack "core") (T.pack "int")

stack :: Type (V a (Stack a))
stack = NominalType $ TypeName (T.pack "core") (T.pack "stack")

plus :: Global (F Integer :-> F Integer :-> F Integer)
plus = Global (u int -=> u int -=> int) (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global (intRaw -=> intRaw -=> int) (T.pack "core") (T.pack "+!")

u :: Type a -> Type (U a)
u x = ApplyType thunk x

infixr 9 -=>

(-=>) :: Type a -> Type b -> Type (a -> b)
a -=> b = ApplyType (ApplyType fnRaw a) b

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
