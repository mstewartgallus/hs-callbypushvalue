{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cbpv (Cbpv (..)) where

import Common
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasTuple

class (HasGlobals t, HasConstants t, HasLet t, HasLetTo t, HasTuple t, HasReturn t) => Cbpv t where
  lambda :: SSet a -> (DataRep t a -> CodeRep t b) -> CodeRep t (a :=> b)
  thunk :: CodeRep t a -> DataRep t (U a)
  force :: DataRep t (U a) -> CodeRep t a
