{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, SystemF (..), HasTuple (..), HasFn (..)) where

-- FIXME !
import Cbpv (HasCall (..), HasReturn (..))
import Common
import HasCode
import HasConstants
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are not yet implemented
class (HasCall t, HasConstants t, HasReturn t, HasFn t, HasTuple t) => SystemF t where
  letBe :: Code t a -> (Code t a -> Code t b) -> Code t b

class HasCode t => HasTuple t where
  pair :: Code t a -> Code t b -> Code t (Pair a b)
  unpair ::
    Code t (Pair a b) ->
    (Code t a -> Code t b -> Code t c) ->
    Code t c

class HasCode t => HasFn t where
  -- | function application
  (<*>) :: Code t (a :-> b) -> Code t a -> Code t b

  lambda :: SAlgebra a -> (Code t a -> Code t b) -> Code t (a :-> b)

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (HasFn t, KnownAlgebra a) => (Code t a -> Code t b) -> Code t (a :-> b)
lam = lambda inferAlgebra

infixl 4 <*>
