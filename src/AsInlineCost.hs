{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module AsInlineCost (Code, Data, Stack, extract, extractData, extractStack, AsInlineCost) where

import Cbpv
import Common
import Control.Category
import qualified Cps
import HasCall
import HasConstants
import HasLet
import HasTuple
import qualified Path
import qualified SystemF
import Prelude hiding ((.), (<*>))

data AsInlineCost

extract :: Code a -> Int
extract (C x) = x

extractData :: Data a -> Int
extractData (D x) = x

extractStack :: Stack a -> Int
extractStack (S x) = x

newtype Code (a :: Algebra) = C Int

newtype Data (a :: Set) = D Int

newtype Stack (a :: Algebra) = S Int

instance HasCall Code where
  call _ = C 1

instance HasConstants Data where
  constant _ = D 0

instance SystemF.HasConstants Code where
  constant _ = C 0

instance HasTuple Code Data where
  pair (D xcost) (D ycost) = D (xcost + ycost + 1)
  ofPair f (D tcost) =
    let C rcost = f (D 0) (D 0)
     in C (tcost + rcost + 1)

instance HasLet Code Data where
  letBe (D xcost) f = C (xcost + fcost)
    where
      C fcost = f (D 0)

instance Cps.HasLabel Code Stack where
  label (S xcost) f = C (xcost + fcost)
    where
      C fcost = f (S 0)

instance HasReturn Code Data where
  returns (D cost) = C (cost + 1)
  letTo (C xcost) f =
    let C fcost = f (D 0)
     in C (xcost + fcost + 1)

instance HasFn Code Data where
  C fcost <*> D xcost = C (fcost + xcost + 1)
  lambda _ f =
    let C fcost = f (D 0)
     in C (fcost + 1)

instance HasThunk Code Data where
  force (D cost) = C (cost + 1)
  thunk (C cost) = D (cost + 1)

instance Cps.HasThunk Code Data Stack where
  thunk _ f =
    let C fcost = f (S 0)
     in D (fcost + 1)
  force (D tcost) (S scost) = C (tcost + scost + 1)

instance Cps.HasReturn Code Data Stack where
  letTo _ f =
    let C fcost = f (D 0)
     in S fcost
  returns (D scost) (S tcost) = C (tcost + scost + 1)

instance Cps.HasFn Code Data Stack where
  D xcost <*> S kcost = S (xcost + kcost + 1)
  lambda (S kcost) f =
    let C fcost = f (D 0) (S 0)
     in C (kcost + fcost + 1)

instance Cps.HasCall Data where
  call _ = D 5

instance SystemF.HasTuple Code where
  pair (C xcost) (C ycost) = C (xcost + ycost + 1)
  ofPair f (C tcost) =
    let C rcost = f (C 0) (C 0)
     in C (tcost + rcost + 1)

instance SystemF.HasLet Code where
  letBe (C xcost) f = C (xcost + fcost)
    where
      C fcost = f (C 0)

instance SystemF.HasFn Code where
  lambda t f =
    let C fcost = Path.flatten f (C 0)
     in C (fcost + 1)
  C fcost <*> C xcost = C (fcost + xcost + 1)
