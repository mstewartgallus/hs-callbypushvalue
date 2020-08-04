{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemFSimplifier (Code, extract, Simplifier) where

import Common
import Control.Category
import HasCall
import NatTrans
import Path (Path)
import qualified Path
import SystemF
import Prelude hiding ((.), (<*>))

extract :: Code t :~> t
extract = NatTrans $ \(C _ x) -> x

data Simplifier t

data MaybeFn t a where
  Fn :: (Path (->) (t a) (t b)) -> MaybeFn t (a :-> b)
  NotFn :: MaybeFn t a

data Code t a = C (MaybeFn t a) (t a)

instance HasCall t => HasCall (Code t) where
  call = C NotFn . call

instance HasConstants t => HasConstants (Code t) where
  constant = C NotFn . constant

instance HasTuple t => HasTuple (Code t) where
  pair (C _ x) (C _ y) = C NotFn (pair x y)
  ofPair f (C _ tuple) = C NotFn $ unpair tuple $ \x y ->
    case f (C NotFn x) (C NotFn y) of
      C _ r -> r

instance HasLet t => HasLet (Code t) where
  whereIs f (C _ x) = C NotFn $ letBe x $ \x' -> case f (C NotFn x') of
    C _ y -> y

instance (HasLet t, HasFn t) => HasFn (Code t) where
  lambda t f =
    let f' = Path.make (extract #) . f . Path.make (C NotFn)
     in C (Fn f') $ lambda t f'

  C NotFn f <*> C _ x = C NotFn (f <*> x)
  C (Fn f) _ <*> C _ x = C NotFn (whereIs (Path.flatten f) x)
