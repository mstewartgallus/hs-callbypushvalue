module HasLetLabel (HasLetLabel (..)) where

import HasCode
import HasStack

class (HasStack t, HasCode t) => HasLetLabel t where
  letLabel :: Stack t a -> (Stack t a -> Code t b) -> Code t b
