{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasGlobals (HasGlobals (..)) where

import Common
import Global
import HasCode

class HasCode t => HasGlobals t where
  global :: Global a -> Code t a
