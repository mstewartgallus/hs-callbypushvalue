{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cbpv (Cbpv, HasReturn (..), HasFn (..), HasThunk (..)) where

import Common
import HasCall
import HasConstants
import HasLet
import HasTuple

class (HasCall cd, HasConstants dta, HasLet cd dta, HasReturn cd dta, HasThunk cd dta, HasFn cd dta, HasTuple cd dta) => Cbpv cd dta

instance (HasCall cd, HasConstants dta, HasLet cd dta, HasReturn cd dta, HasThunk cd dta, HasFn cd dta, HasTuple cd dta) => Cbpv cd dta

class HasReturn cd dta | cd -> dta, dta -> cd where
  letTo :: cd ('F a) -> (dta a -> cd b) -> cd b
  letTo = flip from
  from :: (dta a -> cd b) -> cd ('F a) -> cd b
  from = flip letTo

  returns :: dta a -> cd ('F a)

class HasFn cd dta | cd -> dta, dta -> cd where
  lambda :: SSet a -> (dta a -> cd b) -> cd (a ':=> b)
  (<*>) :: cd (a ':=> b) -> dta a -> cd b

infixl 4 <*>

class HasThunk cd dta | cd -> dta, dta -> cd where
  thunk :: cd a -> dta ('U a)
  force :: dta ('U a) -> cd a
