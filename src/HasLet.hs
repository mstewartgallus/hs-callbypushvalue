{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module HasLet (HasLet (..)) where

import Common

class HasLet (cd :: Algebra -> *) (dta :: Set -> *) | cd -> dta, dta -> cd where
  whereIs :: (dta a -> cd b) -> dta a -> cd b
  whereIs = flip letBe

  letBe :: dta a -> (dta a -> cd b) -> cd b
  letBe = flip whereIs
