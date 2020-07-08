{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Type (applyType, equalType, Type (..)) where

import Common
import Data.Typeable
import Kind
import Name (Name)
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
equalType _ _ = Nothing

instance TextShow (Type a) where
  showb (NominalType _ name) = showb name
  showb (VariableType v) = showb v
  showb a@(ApplyType _ _) = fromString "(" <> loop a <> fromString ")"

loop :: Type a -> Builder
loop (ApplyType f x) = showb f <> fromString " " <> loop x
loop x = showb x
