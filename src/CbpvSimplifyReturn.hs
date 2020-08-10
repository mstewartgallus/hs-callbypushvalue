{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyReturn (Simplifier, extract) where

import Cbpv
import Common
import Control.Category
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTerminal
import HasTuple
import NatTrans
import Path
import Prelude hiding ((.), (<*>), id)

extract :: Code (Simplifier t) :~> Code t
extract = NatTrans cout

data Simplifier t

data Ctx t a b where
  LetToCtx :: (HasLet t, HasReturn t) => (Data t a -> Code t b) -> Ctx t (Code t (F a)) (Code t b)
  ReturnCtx :: HasReturn t => Ctx t (Data t a) (Code t (F a))

flatten :: Path (Ctx t) a b -> a -> b
flatten x = case x of
  Id -> id
  LetToCtx f :.: (ReturnCtx :.: g) -> whereIs f . flatten g
  LetToCtx f :.: g -> from f . flatten g
  ReturnCtx :.: g -> returns . flatten g

cin :: Code t a -> Code (Simplifier t) a
cin code = C $ \ctx -> flatten ctx code

cout :: Code (Simplifier t) a -> Code t a
cout (C f) = f Id

din :: Data t a -> Data (Simplifier t) a
din val = D $ \ctx -> flatten ctx val

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x Id

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns (D x) = C $ \ctx -> x (ctx . (ReturnCtx :.: Id))
  from f (C x) = C $ \ctx -> x (ctx . (LetToCtx (cout . f . din) :.: Id))

instance HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (forall b. Path (Ctx t) (Code t a) b -> b)

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (forall b. Path (Ctx t) (Data t a) b -> b)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasTerminal t => HasTerminal (Simplifier t) where
  terminal = din terminal

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasTuple t => HasTuple (Simplifier t)

instance HasFn t => HasFn (Simplifier t) where
  lambda t f = cin $ lambda t (cout . f . din)
  f <*> x = cin $ (cout f <*> dout x)

instance HasThunk t => HasThunk (Simplifier t) where
  force = cin . force . dout
  thunk = din . thunk . cout
