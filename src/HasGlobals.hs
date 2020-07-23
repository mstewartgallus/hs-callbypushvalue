module HasGlobals (HasGlobals (..)) where

import Global
import HasCode

class HasCode t => HasGlobals t where
  global :: Global a -> Code t a
