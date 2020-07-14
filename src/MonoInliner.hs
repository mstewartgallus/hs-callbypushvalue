{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module MonoInliner (MonoInliner (..)) where

import Common
import qualified TextShow
import qualified Unique

-- | Tagless final newtype to inline letBe clauses that use the bound
-- term one or less times.
--
-- Basically the same as Cost inliner but only measures how often a
-- variable occurs.  Everytime we make this check we make a probe with
-- Mono 1 in letBe.  Nothing else should add a constant amount.
data MonoInliner t (a :: Alg) = M Int (t a)
