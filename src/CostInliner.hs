{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module CostInliner (extract, CostInliner (..)) where

import Basic
import qualified Callcc
import qualified Cbpv
import Common
import qualified Const
import qualified Data.Text as T
import qualified Explicit
import Global
import Name
import SystemF
import TextShow
import qualified Tuple
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

instance Basic t => Basic (CostInliner t) where
  data AlgRep (CostInliner t) a = I Int (AlgRep t a)
  global g = I 0 (global g)

instance SystemF t => SystemF (CostInliner t) where
  constant k = I 0 (constant k)

  pair (I xcost x) (I ycost y) = I (xcost + ycost + 1) (pair x y)

  letBe (I xcost x) f = result
    where
      result
        | xcost <= 3 = inlined
        | otherwise = notinlined
      inlined@(I fcost _) = f (I 0 x)
      notinlined = I (xcost + fcost + 1) $ letBe x $ \x' -> case f (I 0 x') of
        I _ y -> y

  lambda t f = result
    where
      I fcost _ = f (I 0 (global (probe t)))
      result = I (fcost + 1) $ lambda t $ \x' -> case f (I 0 x') of
        I _ y -> y
  I fcost f <*> I xcost x = I (fcost + xcost + 1) (f <*> x)

probe :: SAlg a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
