{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module MonoInliner (Code, Data, Stack, extract, extractData, MonoInliner) where

import Cbpv
import Common
import Control.Category
import qualified Cps
import HasCall
import HasConstants
import HasLet
import HasTuple
import NatTrans
import qualified Path
import qualified SystemF
import Prelude hiding ((.), (<*>))

data MonoInliner t

extract :: Code cd dta k :~> cd
extract = NatTrans $ \(C _ x) -> x

extractData :: Data cd dta k :~> dta
extractData = NatTrans $ \(D _ x) -> x

data Code cd (dta :: Set -> *) (k :: Algebra -> *) (a :: Algebra) = C Int (cd a)

data Data (cd :: Algebra -> *) dta (k :: Algebra -> *) (a :: Set) = D Int (dta a)

data Stack (cd :: Algebra -> *) (dta :: Set -> *) k (a :: Algebra) = S Int (k a)

instance HasCall cd => HasCall (Code cd dta k) where
  call g = C 0 (call g)

instance HasConstants dta => HasConstants (Data cd dta k) where
  constant k = D 0 (constant k)

instance SystemF.HasConstants cd => SystemF.HasConstants (Code cd dta k) where
  constant k = C 0 (SystemF.constant k)

instance HasTuple cd dta => HasTuple (Code cd dta k) (Data cd dta k) where
  pair (D xcost x) (D ycost y) = D (xcost + ycost) (pair x y)
  ofPair f (D tcost tuple) =
    let C rcost _ = f (D 0 undefined) (D 0 undefined)
     in C (tcost + rcost) $ unpair tuple $ \x y -> case f (D 0 x) (D 0 y) of
          C _ r -> r

instance HasLet cd dta => HasLet (Code cd dta k) (Data cd dta k) where
  whereIs f (D xcost x) = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (D 1 x)
      notinlined = C (xcost + fcost) $ letBe x $ \x' -> case f (D 0 x') of
        C _ y -> y
      C fcost _ = f (D 0 x)

instance Cps.HasLabel cd k => Cps.HasLabel (Code cd dta k) (Stack cd dta k) where
  label (S xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (S 1 x)
      notinlined = C (xcost + fcost) $ Cps.label x $ \x' -> case f (S 0 x') of
        C _ y -> y
      C fcost _ = f (S 0 x)

instance HasReturn cd dta => HasReturn (Code cd dta k) (Data cd dta k) where
  returns (D cost k) = C cost (returns k)
  from f (C xcost x) =
    let C fcost _ = f (D 0 undefined)
     in C (xcost + fcost) $ letTo x $ \x' -> case f (D 0 x') of
          C _ y -> y

instance HasFn cd dta => HasFn (Code cd dta k) (Data cd dta k) where
  C fcost f <*> D xcost x = C (fcost + xcost) (f <*> x)
  lambda t f =
    let C fcost _ = f (D 0 undefined)
     in C fcost $ lambda t $ \x' -> case f (D 0 x') of
          C _ y -> y

instance HasThunk cd dta => HasThunk (Code cd dta k) (Data cd dta k) where
  force (D cost th) = C cost (force th)
  thunk (C cost code) = D cost (thunk code)

instance Cps.HasThunk cd dta k => Cps.HasThunk (Code cd dta k) (Data cd dta k) (Stack cd dta k) where
  thunk t f =
    let C fcost _ = f (S 0 undefined)
     in D fcost $ Cps.thunk t $ \x' -> case f (S 0 x') of
          C _ y -> y
  force (D tcost th) (S scost stack) = C (tcost + scost) (Cps.force th stack)

instance Cps.HasReturn cd dta k => Cps.HasReturn (Code cd dta k) (Data cd dta k) (Stack cd dta k) where
  letTo t f =
    let C fcost _ = f (D 0 undefined)
     in S fcost $ Cps.letTo t $ \x' -> case f (D 0 x') of
          C _ y -> y
  returns (D scost c) (S tcost stk) = C (tcost + scost) (Cps.returns c stk)

instance Cps.HasFn cd dta k => Cps.HasFn (Code cd dta k) (Data cd dta k) (Stack cd dta k) where
  D xcost x <*> S kcost k = S (xcost + kcost) (x Cps.<*> k)
  lambda (S kcost k) f =
    let C fcost _ = f (D 0 undefined) (S 0 undefined)
     in C (kcost + fcost) $ Cps.lambda k $ \x n -> case f (D 0 x) (S 0 n) of
          C _ y -> y

instance Cps.HasCall dta => Cps.HasCall (Data cd dta k) where
  call = D 0 . Cps.call

instance SystemF.HasTuple cd => SystemF.HasTuple (Code cd dta k) where
  pair (C xcost x) (C ycost y) = C (xcost + ycost) (SystemF.pair x y)
  ofPair f (C tcost tuple) =
    let C rcost _ = f (C 0 undefined) (C 0 undefined)
     in C (tcost + rcost) $ SystemF.unpair tuple $ \x y -> case f (C 0 x) (C 0 y) of
          C _ r -> r

instance SystemF.HasLet cd => SystemF.HasLet (Code cd dta k) where
  whereIs f (C xcost x) = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (C 1 x)
      notinlined = C (xcost + fcost) $ SystemF.letBe x $ \x' -> case f (C 0 x') of
        C _ y -> y
      C fcost _ = f (C 0 x)

instance SystemF.HasFn cd => SystemF.HasFn (Code cd dta k) where
  lambda t f =
    let C fcost _ = Path.flatten f (C 0 undefined)
     in C fcost $ SystemF.lambda t (Path.make (extract #) . f . Path.make (C 0))
  C fcost f <*> C xcost x = C (fcost + xcost) (f SystemF.<*> x)
