{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module SystemF.Type
  ( equalType,
    Unit,
    type (*),
    U64,
    Void,
    type (~>),
    Type,
    SType (..),
    inferType,
    KnownType (..)
  )
where

import Data.Proxy
import Data.Typeable
import TextShow

type Unit = 'Unit
type (*) = '(:*:)

infixr 0 *

type U64 = 'U64

type Void = 'Void

type (~>) = '(:~>)

infixr 9 ~>

type Type = TypeU

data TypeU = Void | Unit | TypeU :*: TypeU | TypeU :~> TypeU | U64

inferType :: KnownType a => SType a
inferType = reifyType Proxy

class KnownType a where
  reifyType :: Proxy a -> SType a

instance KnownType 'U64 where
  reifyType Proxy = SU64

instance KnownType 'Unit where
  reifyType Proxy = SUnit

instance KnownType 'Void where
  reifyType Proxy = SVoid

instance (KnownType x, KnownType y) => KnownType (x ':*: y) where
  reifyType Proxy = SPair (reifyType Proxy) (reifyType Proxy)

instance (KnownType x, KnownType y) => KnownType (x ':~> y) where
  reifyType Proxy = SFn (reifyType Proxy) (reifyType Proxy)

data SType a where
  SU64 :: SType 'U64
  SVoid :: SType 'Void
  SUnit :: SType 'Unit
  SPair :: SType a -> SType b -> SType (a ':*: b)
  SFn :: SType a -> SType b -> SType (a ~> b)

infixr 9 `SFn`

equalType :: SType a -> SType b -> Maybe (a :~: b)
equalType SU64 SU64 = Just Refl
equalType SVoid SVoid = Just Refl
equalType SUnit SUnit = Just Refl
equalType (SPair a b) (SPair a' b') = case (equalType a a', equalType b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalType (SFn a b) (SFn a' b') = case (equalType a a', equalType b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalType _ _ = Nothing

instance TextShow (SType a) where
  showb SU64 = fromString "u64"
  showb SVoid = fromString "void"
  showb SUnit = fromString "unit"
  showb (SPair x y) = fromString "(" <> showb x <> fromString ", " <> showb y <> fromString ")"
  showb (SFn x y) = fromString "(" <> showb x <> fromString " -> " <> showb y <> fromString ")"
