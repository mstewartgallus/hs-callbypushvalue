{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cps (Cps (..)) where

import Common
import Global
import HasCode
import HasConstants
import HasCpsReturn
import HasCpsThunk
import HasData
import HasLet
import HasLetLabel
import HasStack
import HasTuple

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
class (HasConstants t, HasCode t, HasStack t, HasLetLabel t, HasLet t, HasCpsThunk t, HasCpsReturn t, HasTuple t) => Cps t where
  lambda :: Stack t (a ':=> b) -> (Data t a -> Stack t b -> Code t c) -> Code t c
  apply :: Data t a -> Stack t b -> Stack t (a ':=> b)

  nil :: Stack t 'Void
  call :: Global a -> Stack t a -> Code t 'Void
