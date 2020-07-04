{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Common (equalType, V, (:->), Type (..), F, U, Nil, R (..), Stack (..), Label (..), Constant (..), Global (..), AnyGlobal (..), AnyConstant (..), AnyVariable (..), Variable (..)) where

import qualified Data.Text as T
import Data.Typeable
import TextShow
import Unique
import Unsafe.Coerce

data V a b

type a :-> b = U a -> b

infixr 9 :->

data Type a where
  NominalType :: T.Text -> T.Text -> Type a
  ApplyType :: Type (V a b) -> Type a -> Type b

-- fixme... is there a safer way?
equalType :: Type a -> Type b -> Maybe (a :~: b)
equalType (NominalType package name) (NominalType package' name') = if package == package' && name == name' then Just (unsafeCoerce Refl) else Nothing
equalType (ApplyType f x) (ApplyType f' x') = case (equalType f f', equalType x x') of
  (Just Refl, Just Refl) -> Just Refl
  _ -> Nothing
equalType _ _ = Nothing

newtype R = R (IO ())

data F a

type U a = Stack (F (Stack a))

data Nil

data Stack a where
  NilStack :: Stack Nil
  PopStack :: (a -> R) -> Stack (F a)
  PushStack :: a -> Stack b -> Stack (a -> b)

data Variable a = Variable (Type a) Unique

data AnyVariable where
  AnyVariable :: Variable a -> AnyVariable

instance Eq (Variable a) where
  (Variable _ x) == (Variable _ y) = x == y

instance Eq AnyVariable where
  AnyVariable (Variable _ x) == AnyVariable (Variable _ y) = x == y

instance Ord (Variable a) where
  compare (Variable _ x) (Variable _ y) = compare x y

data Label a = Label (Type a) T.Text

data Constant a where
  IntegerConstant :: Integer -> Constant Integer

data AnyConstant where
  AnyConstant :: Constant a -> AnyConstant

instance Eq (Constant a) where
  x == y = AnyConstant x == AnyConstant y

instance Eq AnyConstant where
  AnyConstant (IntegerConstant x) == AnyConstant (IntegerConstant y) = x == y

data Global a = Global (Type a) T.Text T.Text

data AnyGlobal where
  AnyGlobal :: Global a -> AnyGlobal

instance Eq (Global a) where
  (Global _ a x) == (Global _ b y) = a == b && x == y

instance Eq AnyGlobal where
  AnyGlobal (Global _ a x) == AnyGlobal (Global _ b y) = a == b && x == y

instance TextShow (Variable a) where
  showb (Variable _ name) = showb name

instance TextShow (Label a) where
  showb (Label _ name) = fromText name

instance TextShow (Constant a) where
  showb (IntegerConstant n) = showb n

instance TextShow (Global a) where
  showb (Global _ package name) = fromText package <> fromString "/" <> fromText name
