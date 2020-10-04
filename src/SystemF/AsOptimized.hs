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
extract = NatTrans (loop 20)

loop :: Int -> Term (Simplifier t) a -> Term t a
loop n x | n > 0 = loop (n - 1) (opt (step x))
         | otherwise = out x

opt :: Term (Opt t) a -> Term t a
opt x = (CostInliner.extractTerm
          . MonoInliner.extractTerm
          . AsCompose.extractTerm
          . SystemF.Simplifier.extract
          . AsCompose.extractTerm) # x


data Simplifier t

type Opt = SystemF.Simplifier.Simplifier :.: MonoInliner :.: CostInliner

instance HasTerm t => HasTerm (Simplifier t) where
  data Term (Simplifier t) a = C {
    out :: Term t a,
    step :: Term (Opt (Simplifier t)) a
    }

cin :: Term t a -> Term (Simplifier t) a
cin x = C x undefined

cin' :: Term (Opt (Simplifier t)) a -> Term (Simplifier t) a
cin' x = C (out (opt x)) x

instance (HasLet t, HasFn t) => HasFn (Simplifier t) where
  lambda t f = C (lambda t outF) (lambda t optF) where
    outF x = out (f (cin x))
    optF x = step (f (cin' x))
  f <*> x = C (out f <*> out x) (step f <*> step x)

instance HasConstants t => HasConstants (Simplifier t) where
  constant k = C (constant k) (constant k)

instance HasCall t => HasCall (Simplifier t) where
  call k = C (call k) (call k)

instance HasLet t => HasLet (Simplifier t) where
  x `letBe` f = C (out x `letBe` outF) (step x `letBe` optF) where
    outF x' = out (f (cin x'))
    optF x' = step (f (cin' x'))

instance HasTuple t => HasTuple (Simplifier t) where
  first x = C (first (out x)) (first (step x))
  second x = C (second (out x)) (second (step x))
