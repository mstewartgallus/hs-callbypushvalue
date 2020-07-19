{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasLetTo (HasLetTo (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasLetTo t where
  letTo :: Code t (F a) -> (Data t a -> Code t b) -> Code t b
  apply :: Code t (a :=> b) -> Data t a -> Code t b
