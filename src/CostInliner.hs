{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CostInliner (extract, extractData, CostInliner) where

import qualified AsDup
import AsDup (AsDup)
import qualified AsInlineCost
import AsInlineCost (AsInlineCost)
import Cbpv
import Control.Category
import qualified Cps
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple
import NatTrans
import PairF
import qualified Path
import qualified SystemF as F
import Prelude hiding ((.), (<*>))

extract :: Code (CostInliner t) :~> Code t
extract = NatTrans $ \(C x) -> case AsDup.extract # x of
  PairF _ r -> r

extractData :: Data (CostInliner t) :~> Data t
extractData = NatTrans $ \(D x) -> case AsDup.extractData # x of
  PairF _ r -> r

inlineThreshold :: Int
inlineThreshold = 5

instance HasLet t => HasLet (CostInliner t) where
  letBe x f = result
    where
      result
        | AsInlineCost.extractData inlineCost <= inlineThreshold = f x
        | otherwise = notinlined
      PairF inlineCost _ = AsDup.extractData # unD x
      notinlined = C $ letBe (unD x) (unC . f . D)

instance Cps.HasLabel t => Cps.HasLabel (CostInliner t) where
  label x f = result
    where
      result
        | AsInlineCost.extractStack inlineCost <= inlineThreshold = f x
        | otherwise = notinlined
      PairF inlineCost _ = AsDup.extractStack # unS x
      notinlined = C $ Cps.label (unS x) (unC . f . S)

instance F.HasLet t => F.HasLet (CostInliner t) where
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

instance HasData t => HasData (CostInliner t) where
  newtype Data (CostInliner t) a = D {unD :: Data (AsDup AsInlineCost t) a}

instance HasCode t => HasCode (CostInliner t) where
  newtype Code (CostInliner t) a = C {unC :: Code (AsDup AsInlineCost t) a}

instance HasStack t => HasStack (CostInliner t) where
  newtype Stack (CostInliner t) a = S {unS :: Stack (AsDup AsInlineCost t) a}

instance HasCall t => HasCall (CostInliner t) where
  call = C . call

instance HasReturn t => HasReturn (CostInliner t) where
  from f = C . from (unC . f . D) . unC
  returns = C . returns . unD

instance F.HasTuple t => F.HasTuple (CostInliner t) where
  pair (C x) (C y) = C (F.pair x y)
  unpair (C tuple) f = C $ F.unpair tuple $ \x y -> unC $ f (C x) (C y)

instance F.HasFn t => F.HasFn (CostInliner t) where
  lambda t f = C $ F.lambda t (Path.make unC . f . Path.make C)
  C f <*> C x = C (f F.<*> x)

instance HasConstants t => HasConstants (CostInliner t) where
  constant = D . constant

instance F.HasConstants t => F.HasConstants (CostInliner t) where
  constant = C . F.constant

instance HasTuple t => HasTuple (CostInliner t) where
  pair (D x) (D y) = D (pair x y)
  unpair (D tuple) f = C $ unpair tuple $ \x y -> unC $ f (D x) (D y)

instance HasFn t => HasFn (CostInliner t) where
  C f <*> D x = C (f <*> x)
  lambda t f = C $ lambda t (unC . f . D)

instance HasThunk t => HasThunk (CostInliner t) where
  force = C . force . unD
  thunk = D . thunk . unC

instance Cps.HasThunk t => Cps.HasThunk (CostInliner t) where
  thunk t f = D $ Cps.thunk t (unC . f . S)
  force (D th) (S stack) = C (Cps.force th stack)

instance Cps.HasFn t => Cps.HasFn (CostInliner t) where
  lambda (S k) f = C $ Cps.lambda k $ \x n -> unC $ f (D x) (S n)
  D x <*> S k = S (x Cps.<*> k)

instance Cps.HasCall t => Cps.HasCall (CostInliner t) where
  call = D . Cps.call

instance Cps.HasReturn t => Cps.HasReturn (CostInliner t) where
  letTo t f = S $ Cps.letTo t $ \x' -> case f (D x') of
    C y -> y
  returns (D c) (S stk) = C (Cps.returns c stk)
