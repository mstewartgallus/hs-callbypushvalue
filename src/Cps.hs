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
import HasTuple

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
class (HasConstants t, HasThunk t, HasCode t, HasStack t, HasLetLabel t, HasLet t, HasThunk t, HasTuple t) => Cps t where
  throw :: Stack t (F a) -> Data t a -> Code t Void

  letTo :: SSet a -> (Data t a -> Code t Void) -> Stack t (F a)

  apply :: Data t a -> Stack t b -> Stack t (a :=> b)

  nil :: Stack t Void
