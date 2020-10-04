{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF.AsOptimized (Simplifier, extract) where

import SystemF
import Common
import Control.Category
import HasTerm
import NatTrans
import AsCompose ((:.:))
import CostInliner (CostInliner)
import MonoInliner (MonoInliner)
import qualified AsCompose
import qualified CostInliner
import qualified MonoInliner
import qualified SystemF.Simplifier
import Prelude hiding ((.), (<*>), id)

extract :: Term (Simplifier t) :~> Term t
extract = step . NatTrans cout

step :: Term (Opt t) :~> Term t
step = CostInliner.extractTerm
          . MonoInliner.extractTerm
          . AsCompose.extractTerm
          . SystemF.Simplifier.extract
          . AsCompose.extractTerm


data Simplifier t

cin :: Term (Opt t) a -> Term (Simplifier t) a
cin = C

cout :: Term (Simplifier t) a -> Term (Opt t) a
cout (C x) = x

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f = cin (lambda t (cout . f . cin))
  (<*>) f = cin . (<*>) (cout f) . cout

type Opt = SystemF.Simplifier.Simplifier :.: MonoInliner :.: CostInliner

instance HasTerm t => HasTerm (Simplifier t) where
  newtype Term (Simplifier t) a = C (Term (Opt t) a)

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
