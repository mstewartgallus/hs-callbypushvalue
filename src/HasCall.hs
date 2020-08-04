module HasCall (HasCall (..)) where

import Global

class HasCall cd where
  call :: Global a -> cd a
