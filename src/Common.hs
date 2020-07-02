{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Common (compareVariable, V, (:->), Type (..), Name (..), F, U, Stack (..), Label (..), Constant (..), Global (..), AnyGlobal (..), AnyConstant (..), AnyVariable (..), Variable (..)) where
import qualified Data.Text as T
import TextShow
import Data.Dynamic
import Data.Typeable

data V a b

type a :-> b = U a -> b
infixr 9 :->

data Type a where
  Type :: Typeable a => Name a -> Type a

data Name a where
  NominalName :: T.Text -> T.Text -> Name a
  ApplyName :: Name (V a b) -> Name a -> Name b

data F a
type U a = Stack (F (Stack a))

data Stack a where
  PopStack :: (a -> IO ()) -> Stack (F a)
  PushStack :: a -> Stack b -> Stack (a -> b)



data Variable a = Variable (Type a) T.Text
data AnyVariable where
  AnyVariable :: Variable a -> AnyVariable

instance Eq (Variable a) where
  (Variable _ x) == (Variable _ y) = x == y
instance Eq AnyVariable where
  AnyVariable (Variable _ x) == AnyVariable (Variable _ y) = x == y

instance Ord (Variable a) where
  compare (Variable _ x) (Variable _ y) = compare x y


compareVariable :: Variable a -> Variable b -> a -> Maybe b
compareVariable (Variable (Type _) x) (Variable (Type _) y) value = if x == y then fromDynamic (toDyn value) else Nothing



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
  showb (Variable _ name) = fromText name
instance TextShow (Label a) where
  showb (Label _ name) = fromText name
instance TextShow (Constant a) where
  showb (IntegerConstant n) = showb n
instance TextShow (Global a) where
  showb (Global _ package name) = fromText package <> fromString "/" <> fromText name
