{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (equalAlg, equalSet, (:->), Pair, Dict, Kind (..), SSet (..), SAlg (..), Set (..), Alg (..), inferSet, inferAlg, KnownSet (..), KnownAlg (..)) where

import Data.Proxy
import Data.Typeable
import TextShow

data Set = Unit | U Alg | Set :*: Set | U64

infixr 0 :*:

data Alg = Void | F Set | Set :=> Alg

infixr 9 :=>

class Kind (a :: *)

instance Kind Alg

data Dict k = k => Dict

inferSet :: KnownSet a => SSet a
inferSet = reifySet Proxy

inferAlg :: KnownAlg a => SAlg a
inferAlg = reifyAlg Proxy

class KnownSet (a :: Set) where
  reifySet :: Proxy a -> SSet a

class KnownAlg (a :: Alg) where
  reifyAlg :: Proxy a -> SAlg a

instance KnownSet U64 where
  reifySet Proxy = SU64

instance KnownSet Unit where
  reifySet Proxy = SUnit

instance KnownAlg a => KnownSet (U a) where
  reifySet Proxy = SU (reifyAlg Proxy)

instance (KnownSet x, KnownSet y) => KnownSet (x :*: y) where
  reifySet Proxy = SPair (reifySet Proxy) (reifySet Proxy)

instance KnownAlg Void where
  reifyAlg Proxy = SVoid

instance KnownSet a => KnownAlg (F a) where
  reifyAlg Proxy = SF (reifySet Proxy)

instance (KnownSet x, KnownAlg y) => KnownAlg (x :=> y) where
  reifyAlg Proxy = SFn (reifySet Proxy) (reifyAlg Proxy)

data SSet (a :: Set) where
  SU64 :: SSet U64
  SUnit :: SSet Unit
  SU :: SAlg a -> SSet (U a)
  SPair :: SSet a -> SSet b -> SSet (a :*: b)

data SAlg (a :: Alg) where
  SVoid :: SAlg Void
  SF :: SSet a -> SAlg (F a)
  SFn :: SSet a -> SAlg b -> SAlg (a :=> b)

infixr 9 `SFn`

-- Then define the call by name sugarings
type a :-> b = U a :=> b

infixr 9 :->

type Pair a b = F (U a :*: U b)

equalSet :: SSet a -> SSet b -> Maybe (a :~: b)
equalSet SU64 SU64 = Just Refl
equalSet SUnit SUnit = Just Refl
equalSet (SU x) (SU y) = case equalAlg x y of
  Just Refl -> Just Refl
  _ -> Nothing
equalSet (SPair a b) (SPair a' b') = case (equalSet a a', equalSet b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing

equalAlg :: SAlg a -> SAlg b -> Maybe (a :~: b)
equalAlg SVoid SVoid = Just Refl
equalAlg (SF x) (SF y) = case equalSet x y of
  Just Refl -> Just Refl
  _ -> Nothing
equalAlg (SFn a b) (SFn a' b') = case (equalSet a a', equalAlg b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing

instance TextShow (SSet a) where
  showb SU64 = fromString "u64"
  showb SUnit = fromString "unit"
  showb (SU x) = fromString "(U " <> showb x <> fromString ")"
  showb (SPair x y) = fromString "(" <> showb x <> fromString ", " <> showb y <> fromString ")"

instance TextShow (SAlg a) where
  showb SVoid = fromString "void"
  showb (SF x) = fromString "(F " <> showb x <> fromString ")"
  showb (SFn x y) = fromString "(" <> showb x <> fromString " -> " <> showb y <> fromString ")"
