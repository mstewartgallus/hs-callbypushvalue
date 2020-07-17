{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasData (HasData (..)) where

import Common

class HasData t where
  data SetRep t :: Set -> *
