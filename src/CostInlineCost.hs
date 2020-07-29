{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module CostInlineCost (extract, extractData, extractStack, CostInlineCost) where

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
import qualified Path
import qualified SystemF
import Prelude hiding ((.), (<*>))

data CostInlineCost

extract :: Code CostInlineCost a -> Int
extract (C x) = x

extractData :: Data CostInlineCost a -> Int
extractData (D x) = x

extractStack :: Stack CostInlineCost a -> Int
extractStack (S x) = x

instance HasCode CostInlineCost where
  newtype Code CostInlineCost a = C Int

instance HasData CostInlineCost where
  newtype Data CostInlineCost a = D Int

instance HasStack CostInlineCost where
  newtype Stack CostInlineCost a = S Int

instance HasCall CostInlineCost where
  call _ = C 1

instance HasConstants CostInlineCost where
  constant _ = D 0

instance SystemF.HasConstants CostInlineCost where
  constant _ = C 0

instance HasTuple CostInlineCost where
  pair (D xcost) (D ycost) = D (xcost + ycost + 1)
  unpair (D tcost) f =
    let C rcost = f (D 0) (D 0)
     in C (tcost + rcost + 1)

instance HasLet CostInlineCost where
  letBe (D xcost) f = C (xcost + fcost)
    where
      C fcost = f (D 0)

instance Cps.HasLabel CostInlineCost where
  label (S xcost) f = C (xcost + fcost)
    where
      C fcost = f (S 0)

instance HasReturn CostInlineCost where
  returns (D cost) = C (cost + 1)
  letTo (C xcost) f =
    let C fcost = f (D 0)
     in C (xcost + fcost + 1)

instance HasFn CostInlineCost where
  C fcost <*> D xcost = C (fcost + xcost + 1)
  lambda _ f =
    let C fcost = f (D 0)
     in C (fcost + 1)

instance HasThunk CostInlineCost where
  force (D cost) = C (cost + 1)
  thunk (C cost) = D (cost + 1)

instance Cps.HasThunk CostInlineCost where
  thunk _ f =
    let C fcost = f (S 0)
     in D (fcost + 1)
  force (D tcost) (S scost) = C (tcost + scost + 1)

instance Cps.HasReturn CostInlineCost where
  letTo _ f =
    let C fcost = f (D 0)
     in S fcost
  returns (D scost) (S tcost) = C (tcost + scost + 1)

instance Cps.HasFn CostInlineCost where
  D xcost <*> S kcost = S (xcost + kcost + 1)
  lambda (S kcost) f =
    let C fcost = f (D 0) (S 0)
     in C (kcost + fcost + 1)

instance Cps.HasCall CostInlineCost where
  call _ = D 5

instance SystemF.HasTuple CostInlineCost where
  pair (C xcost) (C ycost) = C (xcost + ycost + 1)
  unpair (C tcost) f =
    let C rcost = f (C 0) (C 0)
     in C (tcost + rcost + 1)

instance SystemF.HasLet CostInlineCost where
  letBe (C xcost) f = C (xcost + fcost)
    where
      C fcost = f (C 0)

instance SystemF.HasFn CostInlineCost where
  lambda t f =
    let C fcost = Path.flatten f (C 0)
     in C (fcost + 1)
  C fcost <*> C xcost = C (fcost + xcost + 1)
