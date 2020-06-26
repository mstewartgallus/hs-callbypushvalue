{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Term (Term (..)) where
import Common
import TextShow

data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term a
  GlobalTerm :: Global a -> Term a
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LambdaTerm binder body) = fromString "(λ " <> showb binder <> fromString " → " <> showb body <> fromString ")"
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"
