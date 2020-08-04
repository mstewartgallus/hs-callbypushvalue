{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module SystemF (lam, SystemF, HasLet (..), HasTuple (..), HasFn (..), HasConstants (..)) where

import Common
import Constant
import HasCall
import Path (Path)
import qualified Path
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- This is kind of like an applicative functor as compared to call by
-- push value which is more like a monad (it is literally based on
-- adjoint functors.)
--
-- FIXME: forall and applyType are not yet implemented
class (HasCall t, HasConstants t, HasFn t, HasLet t, HasTuple t) => SystemF t

instance (HasCall t, HasConstants t, HasFn t, HasLet t, HasTuple t) => SystemF t

class HasLet (t :: Algebra -> *) where
  letBe :: t a -> (t a -> t b) -> t b
  letBe = flip whereIs

  whereIs :: (t a -> t b) -> t a -> t b
  whereIs = flip letBe

class HasConstants t where
  constant :: Constant a -> t ('F a)

class HasTuple t where
  pair :: t a -> t b -> t (Pair a b)
  unpair ::
    t (Pair a b) ->
    (t a -> t b -> t c) ->
    t c
  unpair = flip ofPair
  ofPair ::
    (t a -> t b -> t c) ->
    t (Pair a b) ->
    t c
  ofPair = flip unpair

class HasFn t where
  (<*>) :: t (a :-> b) -> t a -> t b
  lambda :: SAlgebra a -> Path (->) (t a) (t b) -> t (a :-> b)

infixl 4 <*>

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (HasFn t, KnownAlgebra a) => (t a -> t b) -> t (a :-> b)
lam f = lambda inferAlgebra (Path.make f)
