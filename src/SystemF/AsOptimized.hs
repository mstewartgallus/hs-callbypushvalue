{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF.AsOptimized (Simplifier, extract) where

import SystemF
import Common
import Control.Category
import HasCall
import HasCode
import NatTrans
import AsCompose ((:.:))
import CostInliner (CostInliner)
import MonoInliner (MonoInliner)
import qualified AsCompose
import qualified CostInliner
import qualified MonoInliner
import qualified SystemF.Simplifier
import Prelude hiding ((.), (<*>), id)

extract :: Code (Simplifier t) :~> Code t
extract = step . NatTrans cout

step :: Code (Opt t) :~> Code t
step = CostInliner.extract
          . MonoInliner.extract
          . AsCompose.extract
          . SystemF.Simplifier.extract
          . AsCompose.extract


data Simplifier t

cin :: Code (Opt t) a -> Code (Simplifier t) a
cin = C

cout :: Code (Simplifier t) a -> Code (Opt t) a
cout (C x) = x

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f = cin (lambda t (cout . f . cin))
  (<*>) f = cin . (<*>) (cout f) . cout

type Opt = SystemF.Simplifier.Simplifier :.: MonoInliner :.: CostInliner

instance HasCode t => HasCode (Simplifier t) where
  newtype Code (Simplifier t) a = C (Code (Opt t) a)
  probeCode = cin . probeCode

instance HasConstants t => HasConstants (Simplifier t) where
  constant = cin . constant

instance HasCall t => HasCall (Simplifier t) where
  call = cin . call

instance HasLet t => HasLet (Simplifier t) where
  whereIs f = cin . whereIs (cout . f . cin) . cout

instance HasTuple t => HasTuple (Simplifier t) where
  pair f g = cin . pair (cout . f . cin) (cout . g . cin) . cout
  first = cin . first . cout
  second = cin . second . cout
