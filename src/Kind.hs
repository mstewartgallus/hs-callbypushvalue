{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Kind (Kind (..)) where

import Common
import TextShow

data Kind a where
  TypeKind :: Kind a
  FunKind :: Kind a -> Kind b -> Kind (V a b)

instance TextShow (Kind a) where
  showb TypeKind = fromString "*"
  showb (FunKind a b) = fromString "(" <> loop a b <> fromString ")"
    where
      loop :: Kind a -> Kind b -> Builder
      loop a (FunKind b c) = showb a <> fromString " → " <> loop b c
      loop a x = showb a <> fromString " → " <> showb x
