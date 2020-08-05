{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemFSimplifier (extract, Simplifier) where

import Common
import Control.Category
import Debug.Trace
import HasCall
import HasCode
import NatTrans
import SystemF
import Prelude hiding ((.), (<*>))

extract :: Code (Simplifier t) :~> Code t
extract = NatTrans $ \(C _ x) -> x

data Simplifier t

data MaybeFn t a where
  Fn :: (Code t a -> Code t b) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

instance HasCode t => HasCode (Simplifier t) where
  data Code (Simplifier t) a = C (MaybeFn t a) (Code t a)

instance HasCall t => HasCall (Simplifier t) where
  call = C NotFn . call

instance HasConstants t => HasConstants (Simplifier t) where
  constant = C NotFn . constant

instance HasTuple t => HasTuple (Simplifier t) where
  pair (C _ x) (C _ y) = C NotFn (pair x y)
  ofPair f (C _ tuple) = C NotFn $ unpair tuple $ \x y ->
    case f (C NotFn x) (C NotFn y) of
      C _ r -> r

instance HasLet t => HasLet (Simplifier t) where
  whereIs f (C _ x) = C NotFn $ letBe x $ \x' -> case f (C NotFn x') of
    C _ y -> y

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' = (extract #) . f . (C NotFn)
     in C (Fn f') $ lambda t f'

  C NotFn f <*> C _ x = C NotFn (f <*> x)
  C (Fn f) _ <*> C _ x = C NotFn (whereIs f x)
