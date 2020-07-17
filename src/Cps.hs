{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cps (Cps (..)) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasLetLabel
import HasStack
import HasThunk
import Tuple

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
class (HasConstants t, HasCode t, HasStack t, HasLetLabel t, HasLet t, HasThunk t, Tuple t) => Cps t where
  throw :: StackRep t (F a) -> DataRep t a -> CodeRep t Void

  letTo :: SSet a -> (DataRep t a -> CodeRep t Void) -> StackRep t (F a)

  apply :: DataRep t a -> StackRep t b -> StackRep t (a :=> b)

  nil :: StackRep t Void
