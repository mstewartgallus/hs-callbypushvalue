{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Common (V, (:->), Type (..), F, U, Stack, Label (..), Constant (..), Global (..), Variable (..)) where
import qualified Data.Text as T
import TextShow

data V a b

type a :-> b = U a -> b
infixr 9 :->

data Type a where
  NominalType :: T.Text -> T.Text -> Type a
  ApplyType :: Type (V a b) -> Type a -> Type b


data F a
type U a = Stack (F (Stack a))

data Stack a



data Variable a = Variable (Type a) T.Text

instance Eq (Variable a) where
  (Variable _ x) == (Variable _ y) = x == y

instance Ord (Variable a) where
  compare (Variable _ x) (Variable _ y) = compare x y


data Label a = Label (Type a) T.Text

data Constant a where
  IntegerConstant :: Integer -> Constant (F Integer)

data Global a = Global (Type a) T.Text T.Text


instance TextShow (Variable a) where
  showb (Variable _ name) = fromText name
instance TextShow (Label a) where
  showb (Label _ name) = fromText name
instance TextShow (Constant a) where
  showb (IntegerConstant n) = showb n
instance TextShow (Global a) where
  showb (Global _ package name) = fromText package <> fromString "/" <> fromText name
