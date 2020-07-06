{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Type (applyType, equalType, Type (..)) where

import Common
import Data.Typeable
import Kind
import Name
import TextShow
import TypeVariable
import Unsafe.Coerce

data Type a where
  NominalType :: Kind a -> Name -> Type a
  VariableType :: TypeVariable a -> Type a
  ApplyType :: Type (V a b) -> Type a -> Type b

applyType :: Type (V a b) -> Type a -> Type b
applyType = ApplyType

-- fixme... is there a safer way?
equalType :: Type a -> Type b -> Maybe (a :~: b)
equalType (NominalType _ name) (NominalType _ name')
  | name == name' = Just (unsafeCoerce Refl)
  | otherwise = Nothing
equalType (VariableType (TypeVariable _ name)) (VariableType (TypeVariable _ name'))
  | name == name' = Just (unsafeCoerce Refl)
  | otherwise = Nothing
equalType (ApplyType f x) (ApplyType f' x') = case (equalType f f', equalType x x') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing

instance TextShow (Type a) where
  showb (NominalType kind name) = showb name
  showb (VariableType v) = showb v
  showb (ApplyType f x) = fromString "(" <> loop f x <> fromString ")"
    where
      loop :: Type a -> Type b -> Builder
      loop a (ApplyType b c) = showb a <> fromString " " <> loop b c
      loop a x = showb a <> fromString " " <> showb x
