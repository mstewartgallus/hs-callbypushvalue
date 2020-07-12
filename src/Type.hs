{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Type (applyType, equalType, equalAction, Action (..), Type (..)) where

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
  ApplyAction :: Type (V a b) -> Action a -> Type b

infixr 9 :=>

data Action a where
  F :: Type a -> Action (F a)
  (:=>) :: Type a -> Action b -> Action (a :=> b)
  VoidType :: Action Void

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
equalType (ApplyAction f x) (ApplyAction f' x') = case (equalType f f', equalAction x x') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalType _ _ = Nothing

equalAction :: Action a -> Action b -> Maybe (a :~: b)
equalAction (F x) (F x') = case equalType x x' of
  Just Refl -> Just Refl
  _ -> Nothing
equalAction (a :=> b) (a' :=> b') = case (equalType a a', equalAction b b') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalAction _ _ = Nothing

instance TextShow (Type a) where
  showb (NominalType _ name) = showb name
  showb (VariableType v) = showb v
  showb x = fromString "(" <> loop x <> fromString ")"

instance TextShow (Action a) where
  showb VoidType = fromString "Void"
  showb x = fromString "(" <> loopAct x <> fromString ")"

instance Show (Type a) where
  show x = toString (showb x)

loop :: Type a -> Builder
loop (ApplyAction f x) = showb f <> fromString " " <> loopAct x
loop (ApplyType f x) = showb f <> fromString " " <> loop x
loop x = showb x

loopAct :: Action a -> Builder
loopAct (F x) = fromString "F " <> showb x
loopAct (a :=> b) = showb a <> fromString " → " <> loopAct b
loopAct VoidType = fromString "Void"
