{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving, ViewPatterns, PatternSynonyms #-}
module Term (simplify, inline, build, Build (..), Term (..)) where
import Common
import TextShow
import VarMap (VarMap)
import qualified VarMap
import qualified Unique
import Compiler
import Control.Monad.State
import Data.Typeable

data Build a where
  VariableBuild :: Variable (U a) -> Build a
  ConstantBuild :: Constant a -> Build (F a)
  GlobalBuild :: Global a -> Build a
  LetBuild :: Build a -> Type (U a) -> (Build a -> Build b) -> Build b
  LambdaBuild :: Type (U a) -> (Build a -> Build b) -> Build (a :-> b)
  ApplyBuild :: Build (a :-> b) -> Build a -> Build b

build ::  Build a -> Unique.Stream -> Term a
build (VariableBuild v) _ = VariableTerm v
build (ConstantBuild v) _ = ConstantTerm v
build (GlobalBuild v) _ = GlobalTerm v
build (ApplyBuild f x) (Split left right) = ApplyTerm (build f left) (build x right)
build (LetBuild term t body) (Pick head (Split left right)) = let
  x = Variable t (toText (showb head))
  term' = build term left
  body' = build (body (VariableBuild x)) right
  in Let term' x body'
build (LambdaBuild t body) (Pick head tail) = let
  x = Variable t (toText (showb head))
  body' = build (body (VariableBuild x)) tail
  in Lambda x body'

data Term a where
  VariableTerm :: Variable (U a) -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  Let :: Term a -> Variable (U a) -> Term b -> Term b
  Lambda :: Variable (U a) -> Term b -> Term (a :-> b)
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
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (Let term binder body) = fromString "let " <> showb term <> fromString " = " <> showb binder <> fromString " in\n" <> showb body <> fromString ""
  showb (Lambda binder body) = fromString "(λ " <> showb binder <> fromString " → " <> showb body <> fromString ")"
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"

pattern Pick head tail <- (Unique.pick -> (head, tail))
pattern Split left right <- (Unique.split -> (left, right))

simplify :: Unique.Stream -> Term a -> Term a
simplify supply (ApplyTerm (LambdaTerm t f) term) = simplify supply (LetTerm term t f)
simplify (Pick head (Split left (Split a b))) (LetTerm term t body) = let
  x = Variable t (toText (showb head))
  term' = simplify left term
  body' = simplify a (body (VariableTerm x))
  in LetTerm term' t (\val ->substitute' x val b body')
simplify (Pick head (Split left right)) (LambdaTerm t body) = let
  x = Variable t (toText (showb head))
  body' = simplify left (body (VariableTerm x))
  in LambdaTerm t (\val -> substitute' x val right body')
simplify (Split left right) (ApplyTerm f x) = ApplyTerm (simplify left f) (simplify right x)
simplify _ t = t

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

data X a where
  X :: Term a -> X (U a)

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
substitute' :: Variable (U b) -> Term b -> Unique.Stream -> Term a -> Term a
substitute' key value = substitute (VarMap.insert key (X value) VarMap.empty)

substitute :: VarMap X -> Unique.Stream -> Term a -> Term a
substitute map = w where
  w :: Unique.Stream -> Term x -> Term x
  w (Pick head (Split left (Split a b))) (LetTerm term t body) = let
    x = Variable t (toText (showb head))
    term' = w left term
    body' = w a (body (VariableTerm x))
    in LetTerm term' t (\val -> substitute' x val b body')
  w _ v@(VariableTerm variable) = case VarMap.lookup variable map of
    Nothing -> v
    Just (X replacement) -> replacement
  w (Split left right) (ApplyTerm f x) = ApplyTerm (w left f) (w right x)
  w (Pick head (Split left right)) (LambdaTerm t body) = let
    x = Variable t (toText (showb head))
    body' = w left (body (VariableTerm x))
    in LambdaTerm t (\val -> substitute' x val right body')
  w _ term = term
