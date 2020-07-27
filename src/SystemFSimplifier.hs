{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemFSimplifier (extract, Simplifier) where

import Common
import HasCall
import HasCode
import SystemF
import Prelude hiding ((<*>))

extract :: Code (Simplifier t) a -> Code t a
extract (C _ x) = x

data Simplifier t

data MaybeFn t a where
  Fn :: (Code t a -> Code t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance HasCode t => HasCode (Simplifier t) where
  data Code (Simplifier t) a = C (MaybeFn t a) (Code t a)

instance HasCall t => HasCall (Simplifier t) where
  call g = C NotFn (call g)

instance HasConstants t => HasConstants (Simplifier t) where
  constant k = C NotFn (constant k)

instance HasTuple t => HasTuple (Simplifier t) where
  pair (C _ x) (C _ y) = C NotFn (pair x y)
  unpair (C _ tuple) f = C NotFn $ unpair tuple $ \x y ->
    case f (C NotFn x) (C NotFn y) of
      C _ r -> r

instance HasLet t => HasLet (Simplifier t) where
  letBe (C _ x) f = C NotFn $ letBe x $ \x' -> case f (C NotFn x') of
    C _ y -> y

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' x' = case f (C NotFn x') of
          C _ y -> y
     in C (Fn f') $ lambda t f'

  C NotFn f <*> C _ x = C NotFn (f <*> x)
  C (Fn f) _ <*> C _ x = C NotFn (letBe x f)
