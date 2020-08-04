{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CostInliner (Code, Data, Stack, extract, extractData, CostInliner) where

import qualified AsDup
import AsDup (AsDup)
import qualified AsInlineCost
import AsInlineCost (AsInlineCost)
import Cbpv
import Control.Category
import qualified Cps
import HasCall
import HasConstants
import HasLet
import HasTuple
import NatTrans
import PairF
import qualified Path
import qualified SystemF as F
import Prelude hiding ((.), (<*>))

extract :: Code cd dta k :~> cd
extract = NatTrans $ \(C x) -> case AsDup.extract # x of
  PairF _ r -> r

extractData :: Data cd dta k :~> dta
extractData = NatTrans $ \(D x) -> case AsDup.extractData # x of
  PairF _ r -> r

inlineThreshold :: Int
inlineThreshold = 5

instance HasLet cd dta => HasLet (Code cd dta k) (Data cd dta k) where
  letBe x f = result
    where
      result
        | AsInlineCost.extractData inlineCost <= inlineThreshold = f x
        | otherwise = notinlined
      PairF inlineCost _ = AsDup.extractData # unD x
      notinlined = C $ letBe (unD x) (unC . f . D)

instance Cps.HasLabel cd k => Cps.HasLabel (Code cd dta k) (Stack cd dta k) where
  label x f = result
    where
      result
        | AsInlineCost.extractStack inlineCost <= inlineThreshold = f x
        | otherwise = notinlined
      PairF inlineCost _ = AsDup.extractStack # unS x
      notinlined = C $ Cps.label (unS x) (unC . f . S)

instance F.HasLet cd => F.HasLet (Code cd dta k) where
  letBe x f = result
    where
      result
        | AsInlineCost.extract inlineCost <= inlineThreshold = f x
        | otherwise = notinlined
      PairF inlineCost _ = AsDup.extract # unC x
      notinlined = C $ F.letBe (unC x) (unC . f . C)

-- | Tagless final newtype to inline letBe clauses based on a simple
-- cost model
--
-- FIXME: for now all the node costs and inline thresholds are
-- arbitrary and will need tuning
--
-- FIXME: use an alternative to the probe function
data CostInliner t

newtype Data cd dta k a = D {unD :: AsDup.Data AsInlineCost.Code AsInlineCost.Data AsInlineCost.Stack cd dta k a}

newtype Code cd dta k a = C {unC :: AsDup.Code AsInlineCost.Code AsInlineCost.Data AsInlineCost.Stack cd dta k a}

newtype Stack cd dta k a = S {unS :: AsDup.Stack AsInlineCost.Code AsInlineCost.Data AsInlineCost.Stack cd dta k a}

instance HasCall cd => HasCall (Code cd dta k) where
  call = C . call

instance HasReturn cd dta => HasReturn (Code cd dta k) (Data cd dta k) where
  from f = C . from (unC . f . D) . unC
  returns = C . returns . unD

instance F.HasTuple cd => F.HasTuple (Code cd dta k) where
  pair (C x) (C y) = C (F.pair x y)
  ofPair f (C tuple) = C $ F.ofPair (\x y -> unC $ f (C x) (C y)) tuple

instance F.HasFn cd => F.HasFn (Code cd dta k) where
  lambda t f = C $ F.lambda t (Path.make unC . f . Path.make C)
  C f <*> C x = C (f F.<*> x)

instance HasConstants dta => HasConstants (Data cd dta k) where
  constant = D . constant

instance F.HasConstants cd => F.HasConstants (Code cd dta k) where
  constant = C . F.constant

instance HasTuple cd dta => HasTuple (Code cd dta k) (Data cd dta k) where
  pair (D x) (D y) = D (pair x y)
  unpair (D tuple) f = C $ unpair tuple $ \x y -> unC $ f (D x) (D y)

instance HasFn cd dta => HasFn (Code cd dta k) (Data cd dta k) where
  C f <*> D x = C (f <*> x)
  lambda t f = C $ lambda t (unC . f . D)

instance HasThunk cd dta => HasThunk (Code cd dta k) (Data cd dta k) where
  force = C . force . unD
  thunk = D . thunk . unC

instance Cps.HasThunk cd dta k => Cps.HasThunk (Code cd dta k) (Data cd dta k) (Stack cd dta k) where
  thunk t f = D $ Cps.thunk t (unC . f . S)
  force (D th) (S stack) = C (Cps.force th stack)

instance Cps.HasFn cd dta k => Cps.HasFn (Code cd dta k) (Data cd dta k) (Stack cd dta k) where
  lambda (S k) f = C $ Cps.lambda k (\x n -> unC $ f (D x) (S n))
  D x <*> S k = S (x Cps.<*> k)

instance Cps.HasCall dta => Cps.HasCall (Data cd dta k) where
  call = D . Cps.call

instance Cps.HasReturn cd dta k => Cps.HasReturn (Code cd dta k) (Data cd dta k) (Stack cd dta k) where
  letTo t f = S $ Cps.letTo t (unC . f . D)
  returns (D c) (S stk) = C (Cps.returns c stk)
