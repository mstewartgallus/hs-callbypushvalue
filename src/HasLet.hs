module HasLet (HasLet (..)) where

import HasCode
import HasData

class (HasData t, HasCode t) => HasLet t where
  letBe :: Data t a -> (Data t a -> Code t b) -> Code t b
