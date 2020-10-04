{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasTerm (HasTerm (..)) where

import qualified Data.Kind
import SystemF.Type

class HasTerm t where
  data Term t :: Type -> Data.Kind.Type
