{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasTerm (HasTerm (..)) where

import Common
import Data.Kind

class HasTerm t where
  data Term t :: Algebra -> Type
