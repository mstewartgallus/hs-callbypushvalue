{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module SystemF (lam, SystemF, HasLet (..), HasTuple (..), HasFn (..)) where

-- FIXME !
import Cbpv (HasCall (..), HasReturn (..))
import Common
import HasCode
import HasConstants
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- This is kind of like an applicative functor as compared to call by
-- push value which is more like a monad (it is literally based on
-- adjoint functors.)
--
-- FIXME: forall and applyType are not yet implemented
class (HasCode t, HasCall t, HasConstants t, HasReturn t, HasFn t, HasLet t, HasTuple t) => SystemF t

instance (HasCode t, HasCall t, HasConstants t, HasReturn t, HasFn t, HasLet t, HasTuple t) => SystemF t

class HasCode t => HasLet t where
  letBe :: Code t a -> (Code t a -> Code t b) -> Code t b

class HasCode t => HasTuple t where
  pair :: Code t a -> Code t b -> Code t (Pair a b)
  unpair ::
    Code t (Pair a b) ->
    (Code t a -> Code t b -> Code t c) ->
    Code t c

class HasCode t => HasFn t where
  (<*>) :: Code t (a :-> b) -> Code t a -> Code t b
  lambda :: SAlgebra a -> (Code t a -> Code t b) -> Code t (a :-> b)

infixl 4 <*>

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (HasFn t, KnownAlgebra a) => (Code t a -> Code t b) -> Code t (a :-> b)
lam = lambda inferAlgebra
