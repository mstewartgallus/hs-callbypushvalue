{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cbpv (Cbpv (..)) where

import Common
import HasCode
import HasConstants
import HasData
import HasFn
import HasGlobals
import HasLet
import HasReturn
import HasThunk
import HasTuple

class (HasGlobals t, HasConstants t, HasLet t, HasReturn t, HasThunk t, HasFn t, HasTuple t) => Cbpv t

instance (HasGlobals t, HasConstants t, HasLet t, HasReturn t, HasThunk t, HasFn t, HasTuple t) => Cbpv t
