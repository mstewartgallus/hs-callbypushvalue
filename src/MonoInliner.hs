{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module MonoInliner (extract, extractData, MonoInliner) where

import Cbpv
import qualified Cps
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple
import qualified SystemF
import Prelude hiding ((<*>))

data MonoInliner t

extract :: Code (MonoInliner t) a -> Code t a
extract (C _ x) = x

extractData :: Data (MonoInliner t) a -> Data t a
extractData (D _ x) = x

instance HasCode t => HasCode (MonoInliner t) where
  data Code (MonoInliner t) a = C Int (Code t a)

instance HasData t => HasData (MonoInliner t) where
  data Data (MonoInliner t) a = D Int (Data t a)

instance HasStack t => HasStack (MonoInliner t) where
  data Stack (MonoInliner t) a = S Int (Stack t a)

instance HasCall t => HasCall (MonoInliner t) where
  call g = C 0 (call g)

instance HasConstants t => HasConstants (MonoInliner t) where
  constant k = D 0 (constant k)

instance SystemF.HasConstants t => SystemF.HasConstants (MonoInliner t) where
  constant k = C 0 (SystemF.constant k)

instance HasTuple t => HasTuple (MonoInliner t) where
  pair (D xcost x) (D ycost y) = D (xcost + ycost) (pair x y)
  unpair (D tcost tuple) f =
    let C rcost _ = f (D 0 undefined) (D 0 undefined)
     in C (tcost + rcost) $ unpair tuple $ \x y -> case f (D 0 x) (D 0 y) of
          C _ r -> r

instance HasLet t => HasLet (MonoInliner t) where
  letBe (D xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (D 1 x)
      notinlined = C (xcost + fcost) $ letBe x $ \x' -> case f (D 0 x') of
        C _ y -> y
      C fcost _ = f (D 0 x)

instance Cps.HasLabel t => Cps.HasLabel (MonoInliner t) where
  label (S xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (S 1 x)
      notinlined = C (xcost + fcost) $ Cps.label x $ \x' -> case f (S 0 x') of
        C _ y -> y
      C fcost _ = f (S 0 x)

instance HasReturn t => HasReturn (MonoInliner t) where
  returns (D cost k) = C cost (returns k)
  letTo (C xcost x) f =
    let -- fixme... figure out a better probe...
        C fcost _ = f (D 0 undefined)
     in C (xcost + fcost) $ letTo x $ \x' -> case f (D 0 x') of
          C _ y -> y

instance HasFn t => HasFn (MonoInliner t) where
  C fcost f <*> D xcost x = C (fcost + xcost) (f <*> x)
  lambda t f =
    let C fcost _ = f (D 0 undefined)
     in C fcost $ lambda t $ \x' -> case f (D 0 x') of
          C _ y -> y

instance HasThunk t => HasThunk (MonoInliner t) where
  force (D cost th) = C cost (force th)
  thunk (C cost code) = D cost (thunk code)

instance Cps.HasThunk t => Cps.HasThunk (MonoInliner t) where
  thunk t f =
    let C fcost _ = f (S 0 undefined)
     in D fcost $ Cps.thunk t $ \x' -> case f (S 0 x') of
          C _ y -> y
  force (D tcost th) (S scost stack) = C (tcost + scost) (Cps.force th stack)

instance Cps.HasReturn t => Cps.HasReturn (MonoInliner t) where
  letTo t f =
    let C fcost _ = f (D 0 undefined)
     in S fcost $ Cps.letTo t $ \x' -> case f (D 0 x') of
          C _ y -> y
  returns (D scost c) (S tcost stk) = C (tcost + scost) (Cps.returns c stk)

instance Cps.HasFn t => Cps.HasFn (MonoInliner t) where
  D xcost x <*> S kcost k = S (xcost + kcost) (x Cps.<*> k)
  lambda (S kcost k) f =
    let C fcost _ = f (D 0 undefined) (S 0 undefined)
     in C (kcost + fcost) $ Cps.lambda k $ \x n -> case f (D 0 x) (S 0 n) of
          C _ y -> y

instance Cps.HasCall t => Cps.HasCall (MonoInliner t) where
  call g = D 0 (Cps.call g)

instance SystemF.HasTuple t => SystemF.HasTuple (MonoInliner t) where
  pair (C xcost x) (C ycost y) = C (xcost + ycost) (SystemF.pair x y)
  unpair (C tcost tuple) f =
    let C rcost _ = f (C 0 undefined) (C 0 undefined)
     in C (tcost + rcost) $ SystemF.unpair tuple $ \x y -> case f (C 0 x) (C 0 y) of
          C _ r -> r

instance SystemF.HasLet t => SystemF.HasLet (MonoInliner t) where
  letBe (C xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (C 1 x)
      notinlined = C (xcost + fcost) $ SystemF.letBe x $ \x' -> case f (C 0 x') of
        C _ y -> y
      C fcost _ = f (C 0 x)

instance SystemF.HasFn t => SystemF.HasFn (MonoInliner t) where
  lambda t f =
    let C fcost _ = f (C 0 undefined)
     in C fcost $ SystemF.lambda t $ \x' -> case f (C 0 x') of
          C _ y -> y
  C fcost f <*> C xcost x = C (fcost + xcost) (f SystemF.<*> x)
