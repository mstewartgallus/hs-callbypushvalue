{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Basic (Basic (..)) where

import Common
import Global
import HasCode

class HasCode t => Basic t where
  global :: Global a -> AlgRep t a
