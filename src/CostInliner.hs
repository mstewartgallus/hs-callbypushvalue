{-# LANGUAGE TypeFamilies #-}

module CostInliner (extract, extractData, CostInliner) where

import qualified Callcc
import Cbpv
import Common
import qualified Cps
import qualified Data.Text as T
import Global
import HasCode
import HasConstants
import qualified HasCpsReturn as Cps
import qualified HasCpsThunk as Cps
import HasData
import HasFn
import HasGlobals
import HasLet
import HasLetLabel
import HasReturn
import HasStack
import HasThunk
import HasTuple
import Name
import qualified SystemF as F
import Prelude hiding ((<*>))

extract :: Code (CostInliner t) a -> Code t a
extract (C _ x) = x

extractData :: Data (CostInliner t) a -> Data t a
extractData (D _ x) = x

-- | Tagless final newtype to inline letBe clauses based on a simple
-- cost model
--
-- FIXME: for now all the node costs and inline thresholds are
-- arbitrary and will need tuning
--
-- FIXME: use an alternative to the probe function
data CostInliner t

instance HasData t => HasData (CostInliner t) where
  data Data (CostInliner t) a = D Int (Data t a)

instance HasCode t => HasCode (CostInliner t) where
  data Code (CostInliner t) a = C Int (Code t a)

instance HasStack t => HasStack (CostInliner t) where
  data Stack (CostInliner t) a = S Int (Stack t a)

instance HasGlobals t => HasGlobals (CostInliner t) where
  global g = C 0 (global g)

instance HasReturn t => HasReturn (CostInliner t) where
  letTo (C xcost x) f =
    let -- fixme... figure out a better probe...
        C fcost _ = f (D 0 undefined)
     in C (xcost + fcost + 1) $ letTo x $ \x' -> case f (D 0 x') of
          C _ y -> y
  returns (D cost k) = C cost (returns k)

instance F.SystemF t => F.SystemF (CostInliner t) where
  pair (C xcost x) (C ycost y) = C (xcost + ycost + 1) (F.pair x y)
  unpair (C tcost tuple) f =
    let C rcost _ = f (C 0 undefined) (C 0 undefined)
     in C (tcost + rcost + 1) $ F.unpair tuple $ \x y -> case f (C 0 x) (C 0 y) of
          C _ r -> r

  letBe (C xcost x) f = result
    where
      result
        | xcost <= 3 = inlined
        | otherwise = notinlined
      inlined@(C fcost _) = f (C 0 x)
      notinlined = C (xcost + fcost + 1) $ F.letBe x $ \x' -> case f (C 0 x') of
        C _ y -> y

  lambda t f = result
    where
      C fcost _ = f (C 0 (global (probe t)))
      result = C (fcost + 1) $ F.lambda t $ \x' -> case f (C 0 x') of
        C _ y -> y
  C fcost f <*> C xcost x = C (fcost + xcost + 1) (f F.<*> x)

instance HasConstants t => HasConstants (CostInliner t) where
  constant k = D 0 (constant k)
  unit = D 0 unit

instance HasTuple t => HasTuple (CostInliner t) where
  pair (D xcost x) (D ycost y) = D (xcost + ycost + 1) (pair x y)
  unpair (D tcost tuple) f =
    let C rcost _ = f (D 0 undefined) (D 0 undefined)
     in C (tcost + rcost + 1) $ unpair tuple $ \x y -> case f (D 0 x) (D 0 y) of
          C _ r -> r

instance HasLet t => HasLet (CostInliner t) where
  letBe (D xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (D 1 x)
      notinlined = C (xcost + fcost + 1) $ letBe x $ \x' -> case f (D 0 x') of
        C _ y -> y
      C fcost _ = f (D 0 x)

instance HasLetLabel t => HasLetLabel (CostInliner t) where
  letLabel (S xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (S 1 x)
      notinlined = C (xcost + fcost + 1) $ letLabel x $ \x' -> case f (S 0 x') of
        C _ y -> y
      C fcost _ = f (S 0 x)

instance HasFn t => HasFn (CostInliner t) where
  apply (C fcost f) (D xcost x) = C (fcost + xcost + 1) (apply f x)
  lambda t f =
    let C fcost _ = f (D 0 undefined)
     in C (fcost + 1) $ lambda t $ \x' -> case f (D 0 x') of
          C _ y -> y

instance HasThunk t => HasThunk (CostInliner t) where
  force (D cost th) = C (cost + 1) (force th)
  thunk (C cost code) = D (cost + 1) (thunk code)

instance Cps.HasCpsThunk t => Cps.HasCpsThunk (CostInliner t) where
  thunk t f =
    let C fcost _ = f (S 0 undefined)
     in D (fcost + 1) $ Cps.thunk t $ \x' -> case f (S 0 x') of
          C _ y -> y
  force (D tcost th) (S scost stack) = C (tcost + scost + 1) (Cps.force th stack)

instance Cps.Cps t => Cps.Cps (CostInliner t) where
  lambda (S kcost k) f =
    let C fcost _ = f (D 0 undefined) (S 0 undefined)
     in C (kcost + fcost + 1) $ Cps.lambda k $ \x n -> case f (D 0 x) (S 0 n) of
          C _ y -> y
  apply (D xcost x) (S kcost k) = S (xcost + kcost) $ Cps.apply x k
  call g (S kcost k) = C (kcost + 1) (Cps.call g k)
  nil = S 0 Cps.nil

instance Callcc.Callcc t => Callcc.Callcc (CostInliner t) where
  catch t f =
    let C fcost _ = f (S 0 undefined)
     in C (fcost + 1) $ Callcc.catch t $ \x' -> case f (S 0 x') of
          C _ y -> y
  throw (S scost stack) (C xcost x) = C (scost + xcost + 1) (Callcc.throw stack x)

instance Cps.Cps t => Cps.HasCpsReturn (CostInliner t) where
  letTo t f =
    let C fcost _ = f (D 0 undefined)
     in S fcost $ Cps.letTo t $ \x' -> case f (D 0 x') of
          C _ y -> y

  throw (S tcost stk) (D scost c) = C (tcost + scost) (Cps.throw stk c)

probe :: SAlgebra a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
