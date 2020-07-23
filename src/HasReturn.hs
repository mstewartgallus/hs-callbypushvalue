{-# LANGUAGE DataKinds #-}

module HasReturn (HasReturn (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasReturn t where
  returns :: Data t a -> Code t ('F a)
