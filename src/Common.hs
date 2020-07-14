{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (equalAlg, equalSet, (:->), Pair, Kind (..), SSet (..), SAlg (..), Set (..), Alg (..)) where

import Data.Typeable
import TextShow

data Set = Unit | U Alg | Set :*: Set | U64

infixr 0 :*:

data Alg = Void | F Set | Set :=> Alg

infixr 9 :=>

-- data Kind a where
--   AlgKind :: Kind Alg
--   SetKind :: Kind Set

class Kind (a :: *)

instance Kind Alg

instance Kind Set

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
