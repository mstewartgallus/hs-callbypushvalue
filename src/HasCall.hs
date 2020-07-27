module HasCall (HasCall (..)) where

import Global
import HasCode

class HasCode t => HasCall t where
  call :: Global a -> Code t a
