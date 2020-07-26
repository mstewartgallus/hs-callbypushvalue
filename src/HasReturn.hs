{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module HasReturn (HasReturn (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasReturn t where
  letTo :: Code t ('F a) -> (Data t a -> Code t b) -> Code t b
  returns :: Data t a -> Code t ('F a)
