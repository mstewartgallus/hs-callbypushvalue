{-# LANGUAGE GADTs, TypeOperators #-}
module Term (simplify, inline, build, Build (..), Term (..)) where
import Common
import TextShow
import VarMap (VarMap)
import qualified VarMap
import qualified Unique

data Build a where
  VariableBuild :: Variable (U a) -> Build a
  ConstantBuild :: Constant a -> Build (F a)
  GlobalBuild :: Global a -> Build a
  LetBuild :: Build a -> Type (U a) -> (Build a -> Build b) -> Build b
  LambdaBuild :: Type (U a) -> (Build a -> Build b) -> Build (a :-> b)
  ApplyBuild :: Build (a :-> b) -> Build a -> Build b

build :: Build a -> Unique.Stream -> Term a
build (VariableBuild v) _ = VariableTerm v
build (ConstantBuild v) _ = ConstantTerm v
build (GlobalBuild v) _ = GlobalTerm v
build (ApplyBuild f x) (Unique.Split left right) = ApplyTerm (build f left) (build x right)
build (LetBuild term t body) (Unique.Pick head (Unique.Split left right)) = let
  x = Variable t head
  term' = build term left
  body' = build (body (VariableBuild x)) right
  in LetTerm term' x body'
build (LambdaBuild t body) (Unique.Pick head tail) = let
  x = Variable t head
  body' = build (body (VariableBuild x)) tail
  in LambdaTerm x body'

data Term a where
  VariableTerm :: Variable (U a) -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Variable (U a) -> Term b -> Term b
  LambdaTerm :: Variable (U a) -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

data AnyTerm where
  AnyTerm :: Term a -> AnyTerm

instance Eq AnyTerm where
  AnyTerm x == AnyTerm y = x `eq` y where
    eq :: Term a -> Term b -> Bool
    VariableTerm v `eq` VariableTerm v' = AnyVariable v == AnyVariable v'
    ConstantTerm k `eq` ConstantTerm k' = AnyConstant k == AnyConstant k'
    GlobalTerm g `eq` GlobalTerm g' = AnyGlobal g == AnyGlobal g'
    LetTerm term x f `eq` LetTerm term' x' f' = term `eq` term' && f `eq` f' && AnyVariable x == AnyVariable x'
    LambdaTerm x f `eq` LambdaTerm x' f' = f `eq` f' && AnyVariable x == AnyVariable x'
    ApplyTerm f x `eq` ApplyTerm f' x' = f `eq` f' && x `eq` x'
    _ `eq` _ = False

instance Eq (Term a) where
  x == y = AnyTerm x == AnyTerm y

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = fromString "let " <> showb term <> fromString " = " <> showb binder <> fromString " in\n" <> showb body <> fromString ""
  showb (LambdaTerm binder body) = fromString "(λ " <> showb binder <> fromString " → " <> showb body <> fromString ")"
  showb (ApplyTerm f x) = fromString "(" <> showb f <> fromString " " <> showb x <> fromString ")"

simplify :: Term a -> Build a
simplify = simplify' VarMap.empty

simplify' :: VarMap X -> Term a -> Build a
simplify' map = loop where
  loop :: Term x -> Build x
  loop (ApplyTerm (LambdaTerm binder@(Variable t _) body) term) = let
      term' = loop term
      in LetBuild term' t $ \value -> simplify' (VarMap.insert binder (X value) map) body
  loop (LetTerm term binder@(Variable t _) body) = let
      term' = simplify term
      in LetBuild term' t $ \value -> simplify' (VarMap.insert binder (X value) map) body
  loop (LambdaTerm binder@(Variable t _) body) = let
      body' = simplify body
      in LambdaBuild t $ \value -> simplify' (VarMap.insert binder (X value) map) body
  loop (ApplyTerm f x) = ApplyBuild (loop f) (loop x)
  loop (ConstantTerm c) = ConstantBuild c
  loop (GlobalTerm g) = GlobalBuild g
  loop (VariableTerm v) = case VarMap.lookup v map of
      Just (X x) -> x

count :: Variable a -> Term b -> Int
count v = w where
  w :: Term x -> Int
  w (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
  w (LetTerm term binder body) = w term + if AnyVariable binder == AnyVariable v then 0 else w body
  w (LambdaTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else w body
  w (ApplyTerm f x) = w f + w x
  w _ = 0

inline :: Term a -> Build a
inline = inline' VarMap.empty

data X a where
  X :: Build a -> X (U a)

inline' :: VarMap X -> Term a -> Build a
inline' map = w where
  w :: Term x -> Build x

  w (LetTerm term binder@(Variable t _) body) = let
        term' = w term
    in if count binder body <= 1
    then inline' (VarMap.insert binder (X term') map) body
    else LetBuild term' t $ \value -> inline' (VarMap.insert binder (X value) map) body

  w v@(VariableTerm variable) = case VarMap.lookup variable map of
    Just (X replacement) -> replacement

  w (ApplyTerm f x) = ApplyBuild (w f) (w x)
  w (LambdaTerm binder@(Variable t _) body) = LambdaBuild t $ \value -> inline' (VarMap.insert binder (X value) map) body
  w (ConstantTerm c) = ConstantBuild c
  w (GlobalTerm g) = GlobalBuild g
