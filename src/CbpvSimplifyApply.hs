{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CbpvSimplifyApply (Simplifier, extract) where

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
  ApplyCtx :: (HasLet t, HasFn t) => Data t a -> Ctx t (Code t (a :=> b)) (Code t b)
  LambdaCtx :: HasFn t => SSet a -> (Data t a -> Code t b) -> Ctx t (Data t Unit) (Code t (a :=> b))

cin :: Code t a -> Code (Simplifier t) a
cin code = C code Id

cout :: Code (Simplifier t) a -> Code t a
cout (C x f) = flatten f x

flatten :: Path (Ctx t) a b -> a -> b
flatten x = case x of
  Id -> id
  ApplyCtx x :.: LambdaCtx _ f :.: _ -> const (whereIs f x)
  ctx :.: g -> eval ctx . flatten g

eval :: Ctx t a b -> a -> b
eval ctx = case ctx of
  ApplyCtx x -> \f -> f <*> x
  LambdaCtx t f -> const $ lambda t f

din :: Data t a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data t a
dout (D x) = x

instance (HasLet t, HasFn t, HasTerminal t) => HasFn (Simplifier t) where
  lambda t f = C terminal (LambdaCtx t (cout . f . din) :.: Id)
  (<*>) (C s f) (D x) = C s (ApplyCtx x :.: f)

instance HasTerminal t => HasTerminal (Simplifier t) where
  terminal = din terminal

instance HasCode (Simplifier t) where
  data Code (Simplifier t) a = forall b. C b (Path (Ctx t) b (Code t a))

instance HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data t a)

instance Cbpv t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = din . pair (dout . f . din) (dout . g . din) . dout
  first = din . first . dout
  second = din . second . dout

instance HasReturn t => HasReturn (Simplifier t) where
  returns = cin . returns . dout
  from f = cin . from (cout . f . din) . cout

instance HasThunk t => HasThunk (Simplifier t) where
  force = cin . force . dout
  thunk = din . thunk . cout
