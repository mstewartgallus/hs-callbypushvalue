{-# LANGUAGE TypeFamilies #-}

module CostInliner (extract, CostInliner (..)) where

import qualified Callcc
import Cbpv
import Common
import qualified Data.Text as T
import Explicit
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import Name
import qualified Pure
import qualified SystemF as F
import Tuple
import qualified Unique
import Prelude hiding ((<*>))

extract :: AlgRep (CostInliner t) a -> AlgRep t a
extract (I _ x) = x

-- | Tagless final newtype to inline letBe clauses based on a simple
-- cost model
--
-- FIXME: for now all the node costs and inline thresholds are
-- arbitrary and will need tuning
--
-- FIXME: use an alternative to the probe function
data CostInliner t

instance HasData t => HasData (CostInliner t) where
  data SetRep (CostInliner t) a = CS Int (SetRep t a)

instance HasCode t => HasCode (CostInliner t) where
  data AlgRep (CostInliner t) a = I Int (AlgRep t a)

instance HasGlobals t => HasGlobals (CostInliner t) where
  global g = I 0 (global g)

instance Pure.Pure t => Pure.Pure (CostInliner t) where
  pure (CS cost k) = I cost (Pure.pure k)

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

instance Tuple t => Tuple (CostInliner t) where
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

instance Explicit t => Explicit (CostInliner t) where
  letTo (I xcost x) f =
    let -- fixme... figure out a better probe...
        I fcost _ = f (CS 0 undefined)
     in I (xcost + fcost + 1) $ letTo x $ \x' -> case f (CS 0 x') of
          I _ y -> y

  lambda t f =
    let I fcost _ = f (CS 0 undefined)
     in I (fcost + 1) $ lambda t $ \x' -> case f (CS 0 x') of
          I _ y -> y

  apply (I fcost f) (CS xcost x) = I (fcost + xcost + 1) (apply f x)

instance Cbpv t => Cbpv (CostInliner t) where
  force (CS cost thunk) = I (cost + 1) (force thunk)
  thunk (I cost code) = CS (cost + 1) (thunk code)

instance Callcc.Callcc t => Callcc.Callcc (CostInliner t) where
  data StackRep (CostInliner t) a = SB Int (Callcc.StackRep t a)

  thunk t f =
    let I fcost _ = f (SB 0 undefined)
     in CS (fcost + 1) $ Callcc.thunk t $ \x' -> case f (SB 0 x') of
          I _ y -> y
  force (CS tcost thunk) (SB scost stack) = I (tcost + scost + 1) (Callcc.force thunk stack)

  catch t f =
    let I fcost _ = f (SB 0 undefined)
     in I (fcost + 1) $ Callcc.catch t $ \x' -> case f (SB 0 x') of
          I _ y -> y
  throw (SB scost stack) (I xcost x) = I (scost + xcost + 1) (Callcc.throw stack x)

probe :: SAlgebra a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
