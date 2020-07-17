{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasLetLabel (HasLetLabel (..)) where

import Common
import HasCode
import HasStack

class (HasStack t, HasCode t) => HasLetLabel t where
  letLabel :: StackRep t a -> (StackRep t a -> CodeRep t b) -> CodeRep t b
