{-# LANGUAGE GADTs, TypeOperators, RankNTypes, ViewPatterns, PatternSynonyms #-}
module Core (
  fn, thunk, stack, pattern (:=>), (-=>), pattern StackType, pattern ThunkType,

  returns,
  int, intRaw, plus, strictPlus
  ) where
import qualified Data.Text as T
import Common
import Data.Typeable
import Unsafe.Coerce

{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}
fn :: Type (V a (V b (a :-> b)))
fn = NominalType (T.pack "core") (T.pack "fn")

-- fixme implement in terms of stack...
thunk :: Type (V a (U a))
thunk = NominalType (T.pack "core") (T.pack "U")

fnRaw :: Type (V a (V b (a -> b)))
fnRaw = NominalType (T.pack "core") (T.pack "fnRaw")

returns :: Type (V a (F a))
returns = NominalType (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = ApplyType returns intRaw

intRaw :: Type Integer
intRaw = NominalType (T.pack "core") (T.pack "int")

stack :: Type (V a (Stack a))
stack = NominalType (T.pack "core") (T.pack "stack")

plus :: Global (F Integer :-> F Integer :-> F Integer)
plus = Global (u int -=> u int -=> int) (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global (intRaw -=> intRaw -=> int) (T.pack "core") (T.pack "+!")

u :: Type a -> Type (U a)
u x = ApplyType thunk x

infixr -=>

(-=>) ::  Type a -> Type b -> Type (a -> b)
a -=> b = ApplyType (ApplyType fnRaw a) b

decompose :: Type (a -> b) -> (Type a, Type b)
decompose (ApplyType (ApplyType f x) y) = let
  Just Refl = equalType f fnRaw
  -- fixme... wtf?
  in (unsafeCoerce x, unsafeCoerce y)

pattern head :=> tail <- (decompose -> (head, tail))

getstacktype :: Type (Stack a) -> Type a
getstacktype (ApplyType f x) = let
  Just Refl = equalType f stack
  -- fixme... wtf?
  in unsafeCoerce x

getthunktype :: Type (U a) -> Type a
getthunktype (ApplyType f x) = let
  Just Refl = equalType f thunk
  -- fixme... wtf?
  in unsafeCoerce x

pattern StackType x <- (getstacktype -> x)
pattern ThunkType x <- (getthunktype -> x)
