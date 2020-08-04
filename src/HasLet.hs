module HasLet (HasLet (..)) where

import HasCode
import HasData

class (HasData t, HasCode t) => HasLet t where
  whereIs :: (Data t a -> Code t b) -> Data t a -> Code t b
  whereIs = flip letBe

  letBe :: Data t a -> (Data t a -> Code t b) -> Code t b
  letBe = flip whereIs
