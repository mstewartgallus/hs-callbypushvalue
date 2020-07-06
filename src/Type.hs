{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Type (applyType, equalName, equalType, TypeName (..), Type (..)) where

import Common
import Data.Typeable
import Name
import TextShow
import Unsafe.Coerce

data TypeName a where
  TypeName :: Name -> TypeName a
  TypeApp :: TypeName (V a b) -> Type a -> TypeName b

data Type a where
  NominalType :: TypeName a -> Type a
  LambdaType :: (Type a -> Type b) -> Type (V a b)

applyType :: Type (V a b) -> Type a -> Type b
applyType (LambdaType f) = f

-- fixme... is there a safer way?
equalName :: TypeName a -> TypeName b -> Maybe (a :~: b)
equalName (TypeName name) (TypeName name')
  | name == name' = Just (unsafeCoerce Refl)
  | otherwise = Nothing
equalName (TypeApp f x) (TypeApp f' x') = case (equalName f f', equalType x x') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing

equalType :: Type a -> Type b -> Maybe (a :~: b)
equalType (NominalType name) (NominalType name') = equalName name name'
equalType _ _ = Nothing

instance TextShow (TypeName a) where
  showb (TypeName name) = showb name
  showb (TypeApp f x) = fromString "(" <> loop f x <> fromString ")"
    where
      loop :: TypeName (V a b) -> Type a -> Builder
      loop t@(TypeName _) x = showb t <> fromString " " <> showb x
      loop (TypeApp f x) y = loop f x <> fromString " " <> showb y

instance TextShow (Type a) where
  showb (NominalType name) = showb name
