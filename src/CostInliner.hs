{-# LANGUAGE TypeFamilies #-}

module CostInliner (extract, extractData, CostInliner (..)) where

import qualified Callcc
import Cbpv
import Common
import qualified Cps
import qualified Data.Text as T
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetLabel
import HasLetTo
import HasReturn
import HasStack
import qualified HasThunk
import HasTuple
import Name
import qualified SystemF as F
import qualified Unique
import Prelude hiding ((<*>))

extract :: CodeRep (CostInliner t) a -> CodeRep t a
extract (I _ x) = x

extractData :: DataRep (CostInliner t) a -> DataRep t a
extractData (CS _ x) = x

-- | Tagless final newtype to inline letBe clauses based on a simple
-- cost model
--
-- FIXME: for now all the node costs and inline thresholds are
-- arbitrary and will need tuning
--
-- FIXME: use an alternative to the probe function
data CostInliner t

instance HasData t => HasData (CostInliner t) where
  data DataRep (CostInliner t) a = CS Int (DataRep t a)

instance HasCode t => HasCode (CostInliner t) where
  data CodeRep (CostInliner t) a = I Int (CodeRep t a)

instance HasStack t => HasStack (CostInliner t) where
  data StackRep (CostInliner t) a = SB Int (StackRep t a)

instance HasGlobals t => HasGlobals (CostInliner t) where
  global g = I 0 (global g)

instance HasReturn t => HasReturn (CostInliner t) where
  returns (CS cost k) = I cost (returns k)

instance F.SystemF t => F.SystemF (CostInliner t) where
  pair (I xcost x) (I ycost y) = I (xcost + ycost + 1) (F.pair x y)

  letBe (I xcost x) f = result
    where
      result
        | xcost <= 3 = inlined
        | otherwise = notinlined
      inlined@(I fcost _) = f (I 0 x)
      notinlined = I (xcost + fcost + 1) $ F.letBe x $ \x' -> case f (I 0 x') of
        I _ y -> y

  lambda t f = result
    where
      I fcost _ = f (I 0 (global (probe t)))
      result = I (fcost + 1) $ F.lambda t $ \x' -> case f (I 0 x') of
        I _ y -> y
  I fcost f <*> I xcost x = I (fcost + xcost + 1) (f F.<*> x)

instance HasConstants t => HasConstants (CostInliner t) where
  constant k = CS 0 (constant k)
  unit = CS 0 unit

instance HasTuple t => HasTuple (CostInliner t) where
  pair (CS xcost x) (CS ycost y) = CS (xcost + ycost + 1) (pair x y)

instance HasLet t => HasLet (CostInliner t) where
  letBe (CS xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(I inlineCost _) = f (CS 1 x)
      notinlined = I (xcost + fcost + 1) $ letBe x $ \x' -> case f (CS 0 x') of
        I _ y -> y
      I fcost _ = f (CS 0 x)

instance HasLetLabel t => HasLetLabel (CostInliner t) where
  letLabel (SB xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(I inlineCost _) = f (SB 1 x)
      notinlined = I (xcost + fcost + 1) $ letLabel x $ \x' -> case f (SB 0 x') of
        I _ y -> y
      I fcost _ = f (SB 0 x)

instance HasLetTo t => HasLetTo (CostInliner t) where
  letTo (I xcost x) f =
    let -- fixme... figure out a better probe...
        I fcost _ = f (CS 0 undefined)
     in I (xcost + fcost + 1) $ letTo x $ \x' -> case f (CS 0 x') of
          I _ y -> y

  apply (I fcost f) (CS xcost x) = I (fcost + xcost + 1) (apply f x)

instance Cbpv t => Cbpv (CostInliner t) where
  lambda t f =
    let I fcost _ = f (CS 0 undefined)
     in I (fcost + 1) $ lambda t $ \x' -> case f (CS 0 x') of
          I _ y -> y
  force (CS cost thunk) = I (cost + 1) (force thunk)
  thunk (I cost code) = CS (cost + 1) (thunk code)

instance HasThunk.HasThunk t => HasThunk.HasThunk (CostInliner t) where
  lambda (SB kcost k) f =
    let I fcost _ = f (CS 0 undefined) (SB 0 undefined)
     in I (kcost + fcost + 1) $ HasThunk.lambda k $ \x n -> case f (CS 0 x) (SB 0 n) of
          I _ y -> y
  thunk t f =
    let I fcost _ = f (SB 0 undefined)
     in CS (fcost + 1) $ HasThunk.thunk t $ \x' -> case f (SB 0 x') of
          I _ y -> y
  force (CS tcost thunk) (SB scost stack) = I (tcost + scost + 1) (HasThunk.force thunk stack)

  call g (SB kcost k) = I (kcost + 1) (HasThunk.call g k)

instance Callcc.Callcc t => Callcc.Callcc (CostInliner t) where
  catch t f =
    let I fcost _ = f (SB 0 undefined)
     in I (fcost + 1) $ Callcc.catch t $ \x' -> case f (SB 0 x') of
          I _ y -> y
  throw (SB scost stack) (I xcost x) = I (scost + xcost + 1) (Callcc.throw stack x)

instance Cps.Cps t => Cps.Cps (CostInliner t) where
  letTo t f =
    let I fcost _ = f (CS 0 undefined)
     in SB fcost $ Cps.letTo t $ \x' -> case f (CS 0 x') of
          I _ y -> y

  throw (SB tcost stk) (CS scost c) = I (tcost + scost) (Cps.throw stk c)

  apply (CS xcost x) (SB kcost k) = SB (xcost + kcost) $ Cps.apply x k

probe :: SAlgebra a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
