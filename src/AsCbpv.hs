{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCbpv (extract, AsCbpv (..)) where

import Basic
import Cbpv
import Common
import Const
import qualified Constant
import Core
import Explicit
import Global
import HasCode
import HasData
import qualified Pure
import qualified SystemF as F
import Tuple

extract :: AlgRep (AsCbpv t) a -> AlgRep t a
extract (AsCbpv x) = x

data AsCbpv t

instance HasCode t => HasCode (AsCbpv t) where
  newtype AlgRep (AsCbpv t) a = AsCbpv (AlgRep t a)

instance HasData t => HasData (AsCbpv t) where
  newtype SetRep (AsCbpv t) a = SetRep (SetRep t a)

instance Basic t => Basic (AsCbpv t) where
  global g = AsCbpv (global g)

instance Const t => Const (AsCbpv t) where
  unit = SetRep unit
  constant k = SetRep (constant k)

instance Pure.Pure t => Pure.Pure (AsCbpv t) where
  pure (SetRep k) = AsCbpv (Pure.pure k)

instance Cbpv t => F.SystemF (AsCbpv t) where
  pair (AsCbpv x) (AsCbpv y) = AsCbpv $ Pure.pure (pair (thunk x) (thunk y))

  letBe (AsCbpv x) f = AsCbpv $ letBe (Cbpv.thunk x) $ \x' ->
    let AsCbpv body = f (AsCbpv (Cbpv.force x'))
     in body
  lambda t f = AsCbpv $ lambda (SU t) $ \x ->
    let AsCbpv body = f (AsCbpv (force x))
     in body
  AsCbpv f <*> AsCbpv x = AsCbpv $ apply f (thunk x)
