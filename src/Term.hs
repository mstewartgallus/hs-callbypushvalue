{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Term (simplifyTerm, Term (..)) where
import Common
import TextShow

data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term a
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Variable a -> Term b -> Term b
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = fromString "let " <> showb term <> fromString " = " <> showb binder <> fromString " in\n" <> showb body <> fromString ""
  showb (LambdaTerm binder body) = fromString "(λ " <> showb binder <> fromString " → " <> showb body <> fromString ")"
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"

simplifyTerm :: Term a -> Term a
simplifyTerm (ApplyTerm (LambdaTerm binder body) term) = simplifyTerm (LetTerm term binder body)

simplifyTerm (LetTerm term binder body) = LetTerm (simplifyTerm term) binder (simplifyTerm body)
simplifyTerm (LambdaTerm binder body) = LambdaTerm binder (simplifyTerm body)
simplifyTerm (ApplyTerm f x) = ApplyTerm (simplifyTerm f) (simplifyTerm x)
simplifyTerm t = t
