{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Term (simplify, Term (..)) where
import Common
import TextShow
import VarMap (VarMap)
import qualified VarMap

data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term a
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Variable a -> Term b -> Term b
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

data AnyTerm where
  AnyTerm :: Term a -> AnyTerm

instance Eq AnyTerm where
  AnyTerm (VariableTerm v) == AnyTerm (VariableTerm v') = AnyVariable v == AnyVariable v'
  AnyTerm (ConstantTerm k) == AnyTerm (ConstantTerm k') = AnyConstant k == AnyConstant k'
  AnyTerm (GlobalTerm g) == AnyTerm (GlobalTerm g') = AnyGlobal g == AnyGlobal g'
  AnyTerm (LetTerm term binder body) == AnyTerm (LetTerm term' binder' body') = AnyTerm term == AnyTerm term' && AnyVariable binder' == AnyVariable binder' && AnyTerm body == AnyTerm body'
  AnyTerm (ApplyTerm f x) == AnyTerm (ApplyTerm f' x') = AnyTerm f == AnyTerm f' && AnyTerm x == AnyTerm x'
  _ == _ = False

instance Eq (Term a) where
  x == y = AnyTerm x == AnyTerm y

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = fromString "let " <> showb term <> fromString " = " <> showb binder <> fromString " in\n" <> showb body <> fromString ""
  showb (LambdaTerm binder body) = fromString "(λ " <> showb binder <> fromString " → " <> showb body <> fromString ")"
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"

simplify :: Term a -> Term a
simplify (ApplyTerm (LambdaTerm binder body) term) = simplify (LetTerm term binder body)
simplify (LetTerm term binder body) = LetTerm (simplify term) binder (simplify body)
simplify (LambdaTerm binder body) = LambdaTerm binder (simplify body)
simplify (ApplyTerm f x) = ApplyTerm (simplify f) (simplify x)
simplify t = t

inline :: VarMap Term -> Term a -> Term a
inline map = w where
  w v@(VariableTerm variable) = case VarMap.lookup variable map of
    Nothing -> v
    Just replacement -> replacement
  w term = term
