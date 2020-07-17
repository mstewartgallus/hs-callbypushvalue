{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasThunk (HasThunk (..)) where

import Common
import HasCode
import HasData
import HasStack

class (HasData t, HasCode t, HasStack t) => HasThunk t where
  thunk :: SAlgebra a -> (StackRep t a -> CodeRep t Void) -> DataRep t (U a)
  force :: DataRep t (U a) -> StackRep t a -> CodeRep t Void
