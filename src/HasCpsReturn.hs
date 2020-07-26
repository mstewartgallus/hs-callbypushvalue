{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasCpsReturn (HasCpsReturn (..)) where

import Common
import HasCode
import HasData
import HasStack

-- | Decomposition of returns type into a into callcc style
class (HasData t, HasCode t, HasStack t) => HasCpsReturn t where
  returns :: Stack t ('F a) -> Data t a -> Code t 'Void
  letTo :: SSet a -> (Data t a -> Code t 'Void) -> Stack t ('F a)
