{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Tuple (Tuple (..)) where

import Common
import Const
import Global

class Const t => Tuple t where
  pair :: SetRep t a -> SetRep t b -> SetRep t (a :*: b)

  -- fixme.. indirect style?
  first :: SetRep t (a :*: b) -> SetRep t a
  second :: SetRep t (a :*: b) -> SetRep t b
