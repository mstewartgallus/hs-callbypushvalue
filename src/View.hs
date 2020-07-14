{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module View (View (..)) where

import Common
import qualified TextShow
import qualified Unique

newtype View a = V (forall s. Unique.Stream s -> TextShow.Builder)
