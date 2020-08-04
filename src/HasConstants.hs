module HasConstants (HasConstants (..)) where

import Constant

class HasConstants dta where
  constant :: Constant a -> dta a
