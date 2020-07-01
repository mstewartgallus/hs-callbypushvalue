{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Core (
  fn, thunk,

  int, intRaw, plus, strictPlus
  ) where
import qualified Data.Text as T
import Common
import Data.Typeable
{-
Define a standard library of call by push value types.
Still not sure how to handle types in a lot of cases.
-}

fn :: (Typeable a, Typeable b) => Type (V a (V b (a :-> b)))
fn = Type $ NominalName (T.pack "core") (T.pack "fn")

thunk :: Typeable a => Type (V a (U a))
thunk = Type $ NominalName (T.pack "core") (T.pack "U")

returns :: Typeable a => Type (V a (F a))
returns = Type $ NominalName (T.pack "core") (T.pack "F")

int :: Type (F Integer)
int = let
  Type returns' = returns
  Type intRaw' = intRaw
  in Type $ ApplyName returns' intRaw'

intRaw :: Type Integer
intRaw = Type $ NominalName (T.pack "core") (T.pack "int")

plus :: Global (F Integer :-> F Integer :-> F Integer)
plus = Global (Type undefined) (T.pack "core") (T.pack "+")

-- fixme...
strictPlus :: Global (Integer -> Integer -> F Integer)
strictPlus = Global (Type undefined) (T.pack "core") (T.pack "+!")
