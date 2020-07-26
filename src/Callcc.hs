{-# LANGUAGE DataKinds #-}

module Callcc (Callcc (..)) where

import Common
import Cps (HasThunk (..))
import HasCode
import HasConstants
import HasFn
import HasGlobals
import HasLet
import HasReturn
import HasStack
import HasTuple

class (HasStack t, HasConstants t, HasGlobals t, HasLet t, HasReturn t, HasFn t, HasThunk t, HasTuple t) => Callcc t where
  catch :: SAlgebra a -> (Stack t a -> Code t 'Void) -> Code t a
  throw :: Stack t a -> Code t a -> Code t 'Void
