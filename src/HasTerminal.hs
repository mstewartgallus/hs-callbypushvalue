module HasTerminal (HasTerminal (..)) where

import Common
import HasData

class HasData t => HasTerminal t where
  terminal :: Data t Unit
