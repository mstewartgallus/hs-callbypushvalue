{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyForce (Simplifier, extract) where

import Cbpv
import Common
import Control.Category
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple
import NatTrans
import Path
import Prelude hiding ((.), (<*>), id)

extract :: Code (Simplifier t) :~> Code t
extract = NatTrans cout

data Simplifier t

data Ctx t a b where
  ThunkCtx :: HasThunk t => Ctx t (Code t a) (Data t (U a))
  ForceCtx :: HasThunk t => Ctx t (Data t (U a)) (Code t a)

flatten :: Path (Ctx t) a b -> a -> b
flatten x = case x of
  Id -> id
  ThunkCtx :.: ForceCtx :.: g -> flatten g
  ForceCtx :.: ThunkCtx :.: g -> flatten g
  ctx :.: g -> eval ctx . flatten g

eval :: Ctx t a b -> a -> b
eval ctx = case ctx of
  ThunkCtx -> thunk
  ForceCtx -> force

cin :: Code t a -> Code (Simplifier t) a
cin code = C $ \ctx -> flatten ctx code

cout :: Code (Simplifier t) a -> Code t a
cout (C f) = f Id

din :: Data t a -> Data (Simplifier t) a
din val = D $ \ctx -> flatten ctx val

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x Id

instance HasThunk t => HasThunk (Simplifier t) where
  thunk (C x) = D $ \ctx -> x (ctx . (ThunkCtx :.: Id))
  force (D x) = C $ \ctx -> x (ctx . (ForceCtx :.: Id))

instance HasFn t => HasFn (Simplifier t) where
  lambda t f = cin $ lambda t (cout . f . din)
  f <*> x = cin $ (cout f <*> dout x)

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (forall b. Path (Ctx t) (Code t a) b -> b)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (forall b. Path (Ctx t) (Data t a) b -> b)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasTuple t => HasTuple (Simplifier t)

instance HasReturn t => HasReturn (Simplifier t) where
  returns = cin . returns . dout
  from f = cin . from (cout . f . din) . cout
