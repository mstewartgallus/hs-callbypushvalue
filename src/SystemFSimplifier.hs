{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemFSimplifier (extract, Simplifier) where

import Common
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasReturn
import SystemF
import Prelude hiding ((<*>))

extract :: SystemF t => Code (Simplifier t) a -> Code t a
extract (C _ x) = x

data Simplifier t

data MaybeFn t a where
  Fn :: (Code t a -> Code t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance HasCode t => HasCode (Simplifier t) where
  data Code (Simplifier t) a = C (MaybeFn t a) (Code t a)

instance HasData t => HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)

instance HasGlobals t => HasGlobals (Simplifier t) where
  global g = C NotFn (global g)

instance HasConstants t => HasConstants (Simplifier t) where
  constant k = D (constant k)
  unit = D unit

instance HasReturn t => HasReturn (Simplifier t) where
  returns (D k) = C NotFn (returns k)

instance SystemF t => SystemF (Simplifier t) where
  pair (C _ x) (C _ y) = C NotFn (pair x y)
  unpair (C _ tuple) f = C NotFn $ unpair tuple $ \x y ->
    case f (C NotFn x) (C NotFn y) of
      C _ r -> r

  letBe (C _ x) f = C NotFn $ letBe x $ \x' -> case f (C NotFn x') of
    C _ y -> y

  lambda t f =
    let f' x' = case f (C NotFn x') of
          C _ y -> y
     in C (Fn f') $ lambda t f'

  C NotFn f <*> C _ x = C NotFn (f <*> x)
  C (Fn f) _ <*> C _ x = C NotFn (letBe x f)
