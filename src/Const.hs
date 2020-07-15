{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Const (Const (..)) where

import Common
import Constant

class Const t where
  data SetRep t :: Set -> *

  constant :: Constant a -> SetRep t a
