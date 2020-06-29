{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Core (
  fn, thunk,

  int, intRaw, plus, strictPlus
  ) where
import qualified Data.Text as T
import Common

{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}

fn :: Type (V a (V b (a :-> b)))
fn = NominalType (T.pack "core") (T.pack "fn")

thunk :: Type (V a (U a))
thunk = NominalType (T.pack "core") (T.pack "U")

returns :: Type (V a (F a))
returns = NominalType (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = ApplyType returns intRaw

intRaw :: Type Integer
intRaw = NominalType (T.pack "core") (T.pack "int")

plus :: Global (F Integer :-> F Integer :-> F Integer)
plus = Global (ApplyType (ApplyType fn int) (ApplyType (ApplyType fn int) int)) (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global undefined (T.pack "core") (T.pack "+!")
