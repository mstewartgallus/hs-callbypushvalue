{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, SystemF (..)) where

-- FIXME !
import Cbpv (HasCall (..), HasReturn (..))
import Common
import HasCode
import HasConstants
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class (HasCall t, HasConstants t, HasReturn t) => SystemF t where
  -- | function application
  (<*>) :: Code t (a :-> b) -> Code t a -> Code t b

  lambda :: SAlgebra a -> (Code t a -> Code t b) -> Code t (a :-> b)

  letBe :: Code t a -> (Code t a -> Code t b) -> Code t b

  pair :: Code t a -> Code t b -> Code t (Pair a b)
  unpair ::
    Code t (Pair a b) ->
    (Code t a -> Code t b -> Code t c) ->
    Code t c

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (SystemF t, KnownAlgebra a) => (Code t a -> Code t b) -> Code t (a :-> b)
lam = lambda inferAlgebra

infixl 4 <*>
