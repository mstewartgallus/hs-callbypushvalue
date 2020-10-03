{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv.Simplify (Simplifier, extract) where

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
import AsCompose ((:.:))
import CostInliner (CostInliner)
import MonoInliner (MonoInliner)
import qualified AsCompose
import qualified CostInliner
import qualified MonoInliner
import qualified Cbpv.SimplifyReturn
import qualified Cbpv.SimplifyForce
import qualified Cbpv.SimplifyApply
import Prelude hiding ((.), (<*>), id)

extract :: Code (Simplifier t) :~> Code t
extract = step . NatTrans cout

step :: Code (Opt t) :~> Code t
step = CostInliner.extract
          . MonoInliner.extract
          . AsCompose.extract
          . Cbpv.SimplifyReturn.extract
          . AsCompose.extract
          . Cbpv.SimplifyApply.extract
          . AsCompose.extract
          . Cbpv.SimplifyForce.extract
          . AsCompose.extract


data Simplifier t

cin :: Code (Opt t) a -> Code (Simplifier t) a
cin = C

cout :: Code (Simplifier t) a -> Code (Opt t) a
cout (C x) = x

din :: Data (Opt t) a -> Data (Simplifier t) a
din = D

dout :: Data (Simplifier t) a -> Data (Opt t) a
dout (D x) = x

instance (HasLet t, HasTerminal t, HasFn t) => HasFn (Simplifier t) where
  lambda t f = cin (lambda t (cout . f . din))
  (<*>) f = cin . (<*>) (cout f) . dout

instance HasTerminal t => HasTerminal (Simplifier t) where
  terminal = din terminal

type Opt = Cbpv.SimplifyForce.Simplifier :.: Cbpv.SimplifyApply.Simplifier :.: Cbpv.SimplifyReturn.Simplifier :.: MonoInliner :.: CostInliner

instance HasCode t => HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (Code (Opt t) a)
  probeCode = cin . probeCode

instance HasData t => HasData (Simplifier t) where
  newtype Data (Simplifier t) a = D (Data (Opt t) a)
  probeData = din . probeData

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

instance (HasLet t, HasReturn t) => HasReturn (Simplifier t) where
  returns = cin . returns . dout
  from f = cin . from (cout . f . din) . cout

instance HasThunk t => HasThunk (Simplifier t) where
  force = cin . force . dout
  thunk = din . thunk . cout
