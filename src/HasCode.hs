{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasCode (HasCode (..)) where

import Common

class HasCode t where
  data AlgRep t :: Algebra -> *
