{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (lam, SystemF (..)) where

import Common
import Constant (Constant)
import qualified Constant
import Core hiding (minus, plus)
import qualified Core
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasReturn
import Name
import Prelude hiding ((<*>))

-- | Type class for the nonstrict System-F Omega intermediate
-- representation
--
-- FIXME: forall and applyType are still experimental
class (HasGlobals t, HasConstants t, HasReturn t) => SystemF t where
  -- | function application
  (<*>) :: CodeRep t (a :-> b) -> CodeRep t a -> CodeRep t b

  lambda :: SAlgebra a -> (CodeRep t a -> CodeRep t b) -> CodeRep t (a :-> b)

  letBe :: CodeRep t a -> (CodeRep t a -> CodeRep t b) -> CodeRep t b

  pair :: CodeRep t a -> CodeRep t b -> CodeRep t (Pair a b)
  unpair ::
    CodeRep t (Pair a b) ->
    (CodeRep t a -> CodeRep t b -> CodeRep t c) ->
    CodeRep t c

-- fixme.. make a module reexporting a bunch of syntactic sugar like this for a nice dsl.
lam :: (SystemF t, KnownAlgebra a) => (CodeRep t a -> CodeRep t b) -> CodeRep t (a :-> b)
lam = lambda inferAlgebra

infixl 4 <*>
