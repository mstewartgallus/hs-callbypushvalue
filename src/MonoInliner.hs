{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module MonoInliner (extract, MonoInliner (..)) where

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

data MonoInliner t

extract :: AlgRep (MonoInliner t) a -> AlgRep t a
extract (M _ x) = x

instance Basic t => Basic (MonoInliner t) where
  data AlgRep (MonoInliner t) a = M Int (AlgRep t a)
  global g = M 0 (global g)

instance SystemF t => SystemF (MonoInliner t) where
  constant k = M 0 (constant k)

  pair (M xcost x) (M ycost y) = M (xcost + ycost) (pair x y)

  letBe (M xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(M inlineCost _) = f (M 1 x)
      notinlined = M (xcost + fcost) $ letBe x $ \x' -> case f (M 0 x') of
        M _ y -> y
      M fcost _ = f (M 0 x)

  lambda t f =
    let M fcost _ = f (M 0 (global (probe t)))
     in M fcost $ lambda t $ \x' -> case f (M 0 x') of
          M _ y -> y
  M fcost f <*> M xcost x = M (fcost + xcost) (f <*> x)

probe :: SAlg a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
