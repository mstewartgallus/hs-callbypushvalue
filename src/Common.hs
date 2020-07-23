{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Common (equalAlg, equalSet, (:->), Pair, SSet (..), SAlgebra (..), Set (..), Algebra (..), inferSet, inferAlgebra, KnownSet (..), KnownAlgebra (..)) where

import Data.Proxy
import Data.Typeable
import TextShow

data Set = Unit | U Algebra | Set :*: Set | U64

infixr 0 :*:

data Algebra = Void | F Set | Set :=> Algebra

infixr 9 :=>

inferSet :: KnownSet a => SSet a
inferSet = reifySet Proxy

inferAlgebra :: KnownAlgebra a => SAlgebra a
inferAlgebra = reifyAlgebra Proxy

class KnownSet a where
  reifySet :: Proxy a -> SSet a

class KnownAlgebra a where
  reifyAlgebra :: Proxy a -> SAlgebra a

instance KnownSet 'U64 where
  reifySet Proxy = SU64

instance KnownSet 'Unit where
  reifySet Proxy = SUnit

instance KnownAlgebra a => KnownSet ('U a) where
  reifySet Proxy = SU (reifyAlgebra Proxy)

instance (KnownSet x, KnownSet y) => KnownSet (x ':*: y) where
  reifySet Proxy = SPair (reifySet Proxy) (reifySet Proxy)

instance KnownAlgebra 'Void where
  reifyAlgebra Proxy = SVoid

instance KnownSet a => KnownAlgebra ('F a) where
  reifyAlgebra Proxy = SF (reifySet Proxy)

instance (KnownSet x, KnownAlgebra y) => KnownAlgebra (x ':=> y) where
  reifyAlgebra Proxy = SFn (reifySet Proxy) (reifyAlgebra Proxy)

data SSet a where
  SU64 :: SSet 'U64
  SUnit :: SSet 'Unit
  SU :: SAlgebra a -> SSet ('U a)
  SPair :: SSet a -> SSet b -> SSet (a ':*: b)

data SAlgebra a where
  SVoid :: SAlgebra 'Void
  SF :: SSet a -> SAlgebra ('F a)
  SFn :: SSet a -> SAlgebra b -> SAlgebra (a ':=> b)

infixr 9 `SFn`

-- Then define the call by name sugarings
type a :-> b = 'U a ':=> b

infixr 9 :->

type Pair a b = 'F ('U a ':*: 'U b)

equalSet :: SSet a -> SSet b -> Maybe (a :~: b)
equalSet SU64 SU64 = Just Refl
equalSet SUnit SUnit = Just Refl
equalSet (SU x) (SU y) = case equalAlg x y of
  Just Refl -> Just Refl
  _ -> Nothing
equalSet (SPair a b) (SPair a' b') = case (equalSet a a', equalSet b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalSet _ _ = Nothing

equalAlg :: SAlgebra a -> SAlgebra b -> Maybe (a :~: b)
equalAlg SVoid SVoid = Just Refl
equalAlg (SF x) (SF y) = case equalSet x y of
  Just Refl -> Just Refl
  _ -> Nothing
equalAlg (SFn a b) (SFn a' b') = case (equalSet a a', equalAlg b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalAlg _ _ = Nothing

instance TextShow (SSet a) where
  showb SU64 = fromString "u64"
  showb SUnit = fromString "unit"
  showb (SU x) = fromString "(U " <> showb x <> fromString ")"
  showb (SPair x y) = fromString "(" <> showb x <> fromString ", " <> showb y <> fromString ")"

instance TextShow (SAlgebra a) where
  showb SVoid = fromString "void"
  showb (SF x) = fromString "(F " <> showb x <> fromString ")"
  showb (SFn x y) = fromString "(" <> showb x <> fromString " -> " <> showb y <> fromString ")"
