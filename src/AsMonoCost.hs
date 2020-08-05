{-# LANGUAGE TypeFamilies #-}

module AsMonoCost (extract, extractData, extractStack, probeData, probeCode, probeStack, AsMonoCost) where

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
import qualified SystemF
import Prelude hiding ((.), (<*>))

data AsMonoCost

probeData :: Data AsMonoCost a
probeData = D 1

probeCode :: Code AsMonoCost a
probeCode = C 1

probeStack :: Stack AsMonoCost a
probeStack = S 1

extract :: Code AsMonoCost a -> Int
extract (C x) = x

extractData :: Data AsMonoCost a -> Int
extractData (D x) = x

extractStack :: Stack AsMonoCost a -> Int
extractStack (S x) = x

instance HasCode AsMonoCost where
  newtype Code AsMonoCost a = C Int

instance HasData AsMonoCost where
  newtype Data AsMonoCost a = D Int

instance HasStack AsMonoCost where
  newtype Stack AsMonoCost a = S Int

instance HasCall AsMonoCost where
  call _ = C 0

instance HasConstants AsMonoCost where
  constant _ = D 0

instance SystemF.HasConstants AsMonoCost where
  constant _ = C 0

instance HasTuple AsMonoCost where
  pair (D xcost) (D ycost) = D (xcost + ycost)
  unpair (D tcost) f =
    let C rcost = f (D 0) (D 0)
     in C (tcost + rcost)

instance HasLet AsMonoCost where
  letBe (D xcost) f = C (xcost + fcost)
    where
      C fcost = f (D 0)

instance Cps.HasLabel AsMonoCost where
  label (S xcost) f = C (xcost + fcost)
    where
      C fcost = f (S 0)

instance HasReturn AsMonoCost where
  returns (D cost) = C (cost)
  letTo (C xcost) f =
    let C fcost = f (D 0)
     in C (xcost + fcost)

instance HasFn AsMonoCost where
  C fcost <*> D xcost = C (fcost + xcost)
  lambda _ f =
    let C fcost = f (D 0)
     in C fcost

instance HasThunk AsMonoCost where
  force (D cost) = C cost
  thunk (C cost) = D cost

instance Cps.HasThunk AsMonoCost where
  thunk _ f =
    let C fcost = f (S 0)
     in D fcost
  force (D tcost) (S scost) = C (tcost + scost)

instance Cps.HasReturn AsMonoCost where
  letTo _ f =
    let C fcost = f (D 0)
     in S fcost
  returns (D scost) (S tcost) = C (tcost + scost)

instance Cps.HasFn AsMonoCost where
  D xcost <*> S kcost = S (xcost + kcost)
  lambda (S kcost) f =
    let C fcost = f (D 0) (S 0)
     in C (kcost + fcost)

instance Cps.HasCall AsMonoCost where
  call _ = D 0

instance SystemF.HasTuple AsMonoCost where
  pair (C xcost) (C ycost) = C (xcost + ycost)
  unpair (C tcost) f =
    let C rcost = f (C 0) (C 0)
     in C (tcost + rcost)

instance SystemF.HasLet AsMonoCost where
  letBe (C xcost) f = C (xcost + fcost)
    where
      C fcost = f (C 0)

instance SystemF.HasFn AsMonoCost where
  lambda t f =
    let C fcost = f (C 0)
     in C fcost
  C fcost <*> C xcost = C (fcost + xcost)
