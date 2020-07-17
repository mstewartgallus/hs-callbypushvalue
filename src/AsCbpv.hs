{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCbpv (extract, AsCbpv (..)) where

import Cbpv
import Common
import qualified Constant
import Core
import Explicit
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasReturn
import HasTuple
import qualified SystemF as F

extract :: CodeRep (AsCbpv t) a -> CodeRep t a
extract (AsCbpv x) = x

data AsCbpv t

instance HasCode t => HasCode (AsCbpv t) where
  newtype CodeRep (AsCbpv t) a = AsCbpv (CodeRep t a)

instance HasData t => HasData (AsCbpv t) where
  newtype DataRep (AsCbpv t) a = DataRep (DataRep t a)

instance HasGlobals t => HasGlobals (AsCbpv t) where
  global g = AsCbpv (global g)

instance HasConstants t => HasConstants (AsCbpv t) where
  unit = DataRep unit
  constant k = DataRep (constant k)

instance HasReturn t => HasReturn (AsCbpv t) where
  returns (DataRep k) = AsCbpv (returns k)

instance Cbpv t => F.SystemF (AsCbpv t) where
  pair (AsCbpv x) (AsCbpv y) = AsCbpv $ returns (pair (thunk x) (thunk y))

  letBe (AsCbpv x) f = AsCbpv $ letBe (Cbpv.thunk x) $ \x' ->
    let AsCbpv body = f (AsCbpv (Cbpv.force x'))
     in body
  lambda t f = AsCbpv $ lambda (SU t) $ \x ->
    let AsCbpv body = f (AsCbpv (force x))
     in body
  AsCbpv f <*> AsCbpv x = AsCbpv $ apply f (thunk x)
