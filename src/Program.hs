{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

module Program (Program (..), interpret) where

import Common
import HasCode

newtype Program k a = Program (forall t. k t => Code t a)

interpret :: k t => Program k a -> Code t a
interpret (Program x) = x
