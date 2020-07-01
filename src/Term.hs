{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Term (simplify, inline, Term (..)) where
import Common
import TextShow
import VarMap (VarMap)
import qualified VarMap
import Compiler
import Control.Monad.State
import Data.Typeable

data Term a where
  VariableTerm :: Variable (U a) -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Type (U a) -> (Term a -> Term b) -> Term b
  LambdaTerm :: Type (U a) -> (Term a -> Term b) -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

data AnyTerm where
  AnyTerm :: Term a -> AnyTerm

instance Eq AnyTerm where
  AnyTerm x == AnyTerm y = evalState (x `eq` y) (CompilerState 0 0) where
    eq :: Term a -> Term b -> Compiler Bool
    VariableTerm v `eq` VariableTerm v' = pure (AnyVariable v == AnyVariable v')
    ConstantTerm k `eq` ConstantTerm k' = pure (AnyConstant k == AnyConstant k')
    GlobalTerm g `eq` GlobalTerm g' = pure (AnyGlobal g == AnyGlobal g')
    LetTerm term t@(Type _) f `eq` LetTerm term' (Type _) f' = do
      x <- getVariable t
      let Just x' = gcast x
      a <- term `eq` term'
      b <- f (VariableTerm x) `eq` f' (VariableTerm x')
      pure (a && b)
    LambdaTerm t@(Type _) f `eq` LambdaTerm (Type _) f' = do
      x <- getVariable t
      let Just x' = gcast x
      f (VariableTerm x) `eq` f' (VariableTerm x')
    ApplyTerm f x `eq` ApplyTerm f' x' = do
      a <- f `eq` f'
      b <- x `eq` x'
      pure (a && b)
    _ `eq` _ = pure False

instance Eq (Term a) where
  x == y = AnyTerm x == AnyTerm y

instance TextShow (Term a) where
  showb term = evalState (process term) (CompilerState 0 0) where
      process :: Term a -> Compiler Builder
      process (VariableTerm v) = pure $ showb v
      process (ConstantTerm k) = pure $ showb k
      process (GlobalTerm g) = pure $ showb g
      process (LetTerm term t f) = do
          x <- getVariable t
          term' <- process term
          body <- process (f (VariableTerm x))
          pure $ fromString "let " <> term' <> fromString " = " <> showb x <> fromString " in\n" <> body <> fromString ""
      process (LambdaTerm t body) = do
          v <- getVariable t
          body' <- process (body (VariableTerm v))
          pure $ fromString "(λ " <> showb v <> fromString " → " <> body' <> fromString ")"
      process (ApplyTerm f x) = do
        f' <- process f
        x' <- process x
        pure (fromString "(" <> f' <> fromString " " <> x' <> fromString ")")

simplify :: Term a -> Term a
simplify (ApplyTerm (LambdaTerm t f) term) = simplify (LetTerm term t f)

-- fixme...
simplify (LetTerm term t f) = LetTerm (simplify term) t (\x -> simplify (f x))
simplify (LambdaTerm t body) = LambdaTerm t (\x -> simplify (body x))

simplify (ApplyTerm f x) = ApplyTerm (simplify f) (simplify x)
simplify t = t

-- count :: Variable a -> Term b -> Int
-- count v = w where
--   w :: Term x -> Int
--   w (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
--   w (LetTerm term binder body) = w term + if AnyVariable binder == AnyVariable v then 0 else w body
--   w (LambdaTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else w body
--   w (ApplyTerm f x) = w f + w x
--   w _ = 0

inline :: Term a -> Term a
inline = id -- inline' VarMap.empty

-- data X a where
--   X :: Term a -> X (U a)

-- inline' :: VarMap X -> Term a -> Term a
-- inline' map = w where
--   w :: Term x -> Term x

--   w (LetTerm term binder body) = if count binder body <= 1
--     then inline' (VarMap.insert binder (X (w term)) map) body
--     else LetTerm (w term) binder (inline' (VarMap.delete binder map) body)

--   w v@(VariableTerm variable) = case VarMap.lookup variable map of
--     Nothing -> v
--     Just (X replacement) -> replacement

--   w (ApplyTerm f x) = ApplyTerm (w f) (w x)
--   w (LambdaTerm binder body) = LambdaTerm binder (inline' (VarMap.delete binder map) body)
--   w term = term
