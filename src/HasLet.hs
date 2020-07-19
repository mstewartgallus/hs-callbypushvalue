{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasLet (HasLet (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasLet t where
  letBe :: Data t a -> (Data t a -> Code t b) -> Code t b
