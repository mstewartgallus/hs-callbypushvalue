{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemFSimplifier (simplify, Simplifier) where

import Common
import Constant (Constant)
import qualified Constant
import Core hiding (minus, plus)
import qualified Core
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasReturn
import Name
import SystemF
import Prelude hiding ((<*>))

-- fixme... factor out ?

simplify :: SystemF t => Code (Simplifier t) a -> Code t a
simplify (S _ x) = x

data Simplifier t

data MaybeFn t a where
  Fn :: (Code t a -> Code t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance HasCode t => HasCode (Simplifier t) where
  data Code (Simplifier t) a = S (MaybeFn t a) (Code t a)

instance HasData t => HasData (Simplifier t) where
  newtype Data (Simplifier t) a = SS (Data t a)

instance HasGlobals t => HasGlobals (Simplifier t) where
  global g = S NotFn (global g)

instance HasConstants t => HasConstants (Simplifier t) where
  constant k = SS (constant k)
  unit = SS unit

instance HasReturn t => HasReturn (Simplifier t) where
  returns (SS k) = S NotFn (returns k)

instance SystemF t => SystemF (Simplifier t) where
  pair (S _ x) (S _ y) = S NotFn (pair x y)

  letBe (S _ x) f = S NotFn $ letBe x $ \x' -> case f (S NotFn x') of
    S _ y -> y

  lambda t f =
    let f' x' = case f (S NotFn x') of
          S _ y -> y
     in S (Fn f') $ lambda t f'

  S NotFn f <*> S _ x = S NotFn (f <*> x)
  S (Fn f) _ <*> S _ x = S NotFn (letBe x f)
