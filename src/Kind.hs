{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Kind (equalKind, Kind (..)) where

import Common
import Data.Typeable
import TextShow
import Unsafe.Coerce

data Kind a where
  TypeKind :: Kind a
  FunKind :: Kind a -> Kind b -> Kind (V a b)

instance TextShow (Kind a) where
  showb TypeKind = fromString "*"
  showb (FunKind a b) = fromString "(" <> loop a b <> fromString ")"

loop :: Kind a -> Kind b -> Builder
loop a (FunKind b c) = showb a <> fromString " → " <> loop b c
loop a x = showb a <> fromString " → " <> showb x

-- fixme... not correct.
equalKind :: Kind a -> Kind b -> Maybe (a :~: b)
equalKind TypeKind TypeKind = Just (unsafeCoerce Refl)
equalKind (FunKind a b) (FunKind a' b') = case (equalKind a a', equalKind b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalKind _ _ = Nothing
