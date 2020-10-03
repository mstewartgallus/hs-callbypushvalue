{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CostInliner (extract, extractData, CostInliner) where

import AsDup (AsDup)
import qualified AsDup
import AsInlineCost (AsInlineCost)
import qualified AsInlineCost
import Cbpv
import Control.Category
import qualified Cps
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTerminal
import HasTuple
import NatTrans
import PairF
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
newtype CostInliner t = CostInliner (AsDup AsInlineCost t)
  deriving
    ( HasCall,
      HasConstants,
      HasReturn,
      HasThunk,
      HasFn,
      HasTuple,
      HasTerminal,
      F.HasConstants,
      F.HasTuple,
      F.HasFn,
      Cps.HasCall,
      Cps.HasReturn,
      Cps.HasFn,
      Cps.HasThunk
    )

instance HasData t => HasData (CostInliner t) where
  newtype Data (CostInliner t) a = D {unD :: Data (AsDup AsInlineCost t) a}

instance HasCode t => HasCode (CostInliner t) where
  newtype Code (CostInliner t) a = C {unC :: Code (AsDup AsInlineCost t) a}

instance HasStack t => HasStack (CostInliner t) where
  newtype Stack (CostInliner t) a = S {unS :: Stack (AsDup AsInlineCost t) a}
