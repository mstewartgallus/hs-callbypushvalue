{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF.Simplifier (extract, Simplifier) where

import Common
import Control.Category
import HasTerm
import NatTrans
import SystemF
import Prelude hiding ((.), (<*>))

extract :: Term (Simplifier t) :~> Term t
extract = NatTrans $ \(C x) -> x IdCtx

data Simplifier t

data Ctx t a b where
  ApplyCtx :: HasFn t => Term t a -> Ctx t (a --> b) b
  IdCtx :: Ctx t a a

instance HasTerm t => HasTerm (Simplifier t) where
  newtype Term (Simplifier t) a = C (forall b. Ctx t a b -> Term t b)

into :: Term t a -> Term (Simplifier t) a
into val = C $ \ctx -> case ctx of
  ApplyCtx x -> val <*> x
  IdCtx -> val

out :: Term (Simplifier t) a -> Term t a
out (C f) = f IdCtx

instance HasCall t => HasCall (Simplifier t) where
  call = into . call

instance HasConstants t => HasConstants (Simplifier t) where
  constant = into . constant

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = into . pair (out . f . into) (out . g . into) . out
  first = into . first . out
  second = into . second . out

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = into . whereIs (out . f . into) . out

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f =
    let f' = out . f . into
     in C $ \ctx -> case ctx of
          ApplyCtx x -> whereIs f' x
          IdCtx -> lambda t f'

  C f <*> x = into $ f (ApplyCtx (out x))
