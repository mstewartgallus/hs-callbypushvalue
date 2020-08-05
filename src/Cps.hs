{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cps (Cps, HasThunk (..), HasReturn (..), HasFn (..), HasCall (..), HasLabel (..)) where

import Common
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
type Cps t = (HasConstants t, HasCall t, HasCode t, HasStack t, HasFn t, HasReturn t, HasThunk t, HasLabel t, HasLet t, HasTuple t)

class HasData t => HasCall t where
  call :: Global a -> Data t ('U a)

class (HasData t, HasCode t, HasStack t) => HasFn t where
  lambda :: Stack t (a ':=> b) -> (Data t a -> Stack t b -> Code t c) -> Code t c
  (<*>) :: Data t a -> Stack t b -> Stack t (a ':=> b)

infixr 4 <*>

-- | Decomposition of returns type into a into callcc style
class (HasData t, HasCode t, HasStack t) => HasReturn t where
  returns :: Data t a -> Stack t ('F a) -> Code t 'Void
  letTo :: SSet a -> (Data t a -> Code t 'Void) -> Stack t ('F a)

-- | Decomposition of thunks into cps style
class (HasData t, HasCode t, HasStack t) => HasThunk t where
  thunk :: SAlgebra a -> (Stack t a -> Code t 'Void) -> Data t ('U a)
  force :: Data t ('U a) -> Stack t a -> Code t 'Void

class (HasStack t, HasCode t) => HasLabel t where
  label :: Stack t a -> (Stack t a -> Code t b) -> Code t b
