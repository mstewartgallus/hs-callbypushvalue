{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cps.AsOptimized (Simplifier, extract) where

import Cps
import Common
import Control.Category
import HasCode
import HasConstants
import HasData
import HasLet
import HasTerminal
import HasTuple
import HasStack
import NatTrans
import AsCompose ((:.:))
import CostInliner (CostInliner)
import MonoInliner (MonoInliner)
import qualified AsCompose
import qualified CostInliner
import qualified MonoInliner
import qualified Cps.SimplifyLet
import qualified Cps.SimplifyForce
import qualified Cps.SimplifyApply
import Prelude hiding ((.), (<*>), id)

extract :: Data (Simplifier t) :~> Data t
extract = step . NatTrans dout

step :: Data (Opt t) :~> Data t
step = CostInliner.extractData
          . MonoInliner.extractData
          . AsCompose.extractData
          . Cps.SimplifyLet.extract
          . AsCompose.extractData
          . Cps.SimplifyApply.extract
          . AsCompose.extractData
          . Cps.SimplifyForce.extract
          . AsCompose.extractData


data Simplifier t

cin :: Code (Opt t) a -> Code (Simplifier t) a
cin = C

cout :: Code (Simplifier t) a -> Code (Opt t) a
cout (C x) = x

din :: Data (Opt t) a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data (Opt t) a
dout (D x) = x

kin :: Stack (Opt t) a -> Stack (Simplifier t) a
kin = K

kout :: Stack (Simplifier t) a -> Stack (Opt t) a
kout (K x) = x

instance (HasLet t, HasLabel t, HasFn t) => HasFn (Simplifier t) where
  x <*> k = kin (dout x <*> kout k)
  lambda k f = cin $ lambda (kout k) $ \x t -> cout (f (din x) (kin t))

instance HasTerminal t => HasTerminal (Simplifier t) where
  terminal = din terminal

type Opt = Cps.SimplifyForce.Simplifier :.: Cps.SimplifyApply.Simplifier :.: Cps.SimplifyLet.Simplifier :.: MonoInliner :.: CostInliner

instance HasCode t => HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (Code (Opt t) a)
  probeCode = cin . probeCode

instance HasData t => HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data (Opt t) a)
  probeData = din . probeData

instance HasStack t => HasStack (Simplifier t) where
  newtype Stack (Simplifier t) a = K (Stack (Opt t) a)

instance HasConstants t => HasConstants (Simplifier t) where
  constant = din . constant

instance HasCall t => HasCall (Simplifier t) where
  call = din . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . din) . dout

instance HasLabel t => HasLabel (Simplifier t) where
  whereLabel f = cin . whereLabel (cout . f . kin) . kout

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = din . pair (dout . f . din) (dout . g . din) . dout
  first = din . first . dout
  second = din . second . dout

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns x k = cin $ returns (dout x) (kout k)
  letTo t f = kin $ letTo t (cout . f . din)

instance (HasLabel t, HasThunk t) => HasThunk (Simplifier t) where
  thunk t f = din $ thunk t (cout . f . kin)
  force x k = cin $ force (dout x) (kout k)
