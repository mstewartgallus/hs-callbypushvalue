{-# LANGUAGE DataKinds #-}

module Callcc (Callcc (..)) where

import Common
import HasCode
import HasConstants
import HasLet
import HasLetTo
import HasReturn
import HasStack
import HasThunk
import HasTuple

class (HasStack t, HasConstants t, HasLet t, HasThunk t, HasLetTo t, HasTuple t, HasReturn t) => Callcc t where
  catch :: SAlgebra a -> (Stack t a -> Code t 'Void) -> Code t a
  throw :: Stack t a -> Code t a -> Code t 'Void
