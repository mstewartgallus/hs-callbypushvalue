{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HasTuple (HasTuple (..)) where

import Common

class HasTuple (cd :: Algebra -> *) (dta :: Set -> *) | cd -> dta, dta -> cd where
  pair :: dta a -> dta b -> dta (a ':*: b)
  unpair :: dta (a ':*: b) -> (dta a -> dta b -> cd c) -> cd c
  ofPair :: (dta a -> dta b -> cd c) -> dta (a ':*: b) -> cd c
