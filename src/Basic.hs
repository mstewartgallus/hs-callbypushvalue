{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Basic (Basic (..)) where

import Common
import Global

class Basic t where
  data AlgRep t :: Alg -> *

  global :: Global a -> AlgRep t a
