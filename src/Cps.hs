{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cps (Cps, HasThunk (..), HasReturn (..), HasFn (..), HasCall (..), HasLabel (..)) where

import Common
import Global
import HasConstants
import HasLet
import HasTuple

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
class (HasConstants dta, HasCall dta, HasFn cd dta k, HasReturn cd dta k, HasThunk cd dta k, HasLabel cd k, HasLet cd dta, HasTuple cd dta) => Cps cd dta k

instance (HasConstants dta, HasCall dta, HasFn cd dta k, HasReturn cd dta k, HasThunk cd dta k, HasLabel cd k, HasLet cd dta, HasTuple cd dta) => Cps cd dta k

class HasCall dta where
  call :: Global a -> dta ('U a)

class HasFn (cd :: Algebra -> *) dta k | cd -> dta, dta -> k, k -> cd where
  lambda :: k (a ':=> b) -> (dta a -> k b -> cd c) -> cd c
  (<*>) :: dta a -> k b -> k (a ':=> b)

infixr 4 <*>

-- | Decomposition of returns type into a into callcc style
class HasReturn cd dta k | cd -> dta, dta -> k, k -> cd where
  returns :: dta a -> k ('F a) -> cd 'Void
  letTo :: SSet a -> (dta a -> cd 'Void) -> k ('F a)

-- | Decomposition of thunks into cps style
class HasThunk cd dta k | cd -> dta, dta -> k, k -> cd where
  thunk :: SAlgebra a -> (k a -> cd 'Void) -> dta ('U a)
  force :: dta ('U a) -> k a -> cd 'Void

class HasLabel (cd :: Algebra -> *) (k :: Algebra -> *) where
  label :: k a -> (k a -> cd b) -> cd b
