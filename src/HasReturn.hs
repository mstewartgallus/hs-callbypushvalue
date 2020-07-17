{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasReturn (HasReturn (..)) where

import Common
import HasCode
import HasData

class (HasData t, HasCode t) => HasReturn t where
  returns :: DataRep t a -> CodeRep t (F a)
