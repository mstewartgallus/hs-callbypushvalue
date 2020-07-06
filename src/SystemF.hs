{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (simplify, inline, build, Builder, SystemF (..), Term (..)) where

import Common
import Core
import TextShow (TextShow, fromString, showb)
import qualified Unique
import VarMap (VarMap)
import qualified VarMap

class SystemF t where
  constant :: Constant a -> t Term (F a)
  global :: Global a -> t Term a
  lambda :: Type a -> (t Term a -> t Term b) -> t Term (a :-> b)
  apply :: t Term (a :-> b) -> t Term a -> t Term b
  letBe :: t Term a -> (t Term a -> t Term b) -> t Term b

newtype Builder t a = Builder {builder :: Unique.State (t a)}

build :: Builder t a -> t a
build (Builder s) = Unique.run s

instance SystemF Builder where
  constant k = (Builder . pure) $ ConstantTerm k
  global g = (Builder . pure) $ GlobalTerm g
  letBe value f = Builder $ do
    value' <- builder value
    let t = typeOf value'
    head <- Unique.uniqueId
    let binder = Variable t head
    body <- builder $ f (Builder $ pure $ VariableTerm binder)
    pure (LetTerm value' binder body)
  lambda t f = Builder $ do
    h <- Unique.uniqueId
    let binder = Variable t h
    body <- builder $ f (Builder $ pure $ VariableTerm binder)
    pure (LambdaTerm binder body)
  apply f x = Builder $ do
    f' <- builder f
    x' <- builder x
    pure (ApplyTerm f' x')

data Term a where
  VariableTerm :: Variable a -> Term a
  ConstantTerm :: Constant a -> Term (F a)
  GlobalTerm :: Global a -> Term a
  LetTerm :: Term a -> Variable a -> Term b -> Term b
  LambdaTerm :: Variable a -> Term b -> Term (a :-> b)
  ApplyTerm :: Term (a :-> b) -> Term a -> Term b

typeOf :: Term a -> Type a
typeOf (VariableTerm (Variable t _)) = t
typeOf (ConstantTerm (IntegerConstant _)) = int
typeOf (GlobalTerm (Global t _ _)) = t
typeOf (LetTerm _ _ body) = typeOf body
typeOf (LambdaTerm (Variable t _) body) = t -#-> typeOf body
typeOf (ApplyTerm f _) =
  let _ :=> result = typeOf f
   in result

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = showb term <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LambdaTerm binder@(Variable t _) body) = fromString "λ " <> showb binder <> fromString ": " <> showb t <> fromString " →\n" <> showb body
  showb (ApplyTerm f x) = showb x <> fromString "\n" <> showb f

simplify :: Term a -> Builder Term a
simplify = simplify' VarMap.empty

simplify' :: VarMap X -> Term a -> Builder Term a
simplify' map = loop
  where
    loop :: Term x -> Builder Term x
    loop (ApplyTerm (LambdaTerm binder@(Variable t _) body) term) =
      let term' = loop term
       in letBe term' $ \value -> simplify' (VarMap.insert binder (X value) map) body
    loop (LetTerm term binder@(Variable t _) body) =
      let term' = simplify term
       in letBe term' $ \value -> simplify' (VarMap.insert binder (X value) map) body
    loop (LambdaTerm binder@(Variable t _) body) =
      let body' = simplify body
       in lambda t $ \value -> simplify' (VarMap.insert binder (X value) map) body
    loop (ApplyTerm f x) = apply (loop f) (loop x)
    loop (ConstantTerm c) = constant c
    loop (GlobalTerm g) = global g
    loop (VariableTerm v) = case VarMap.lookup v map of
      Just (X x) -> x

count :: Variable a -> Term b -> Int
count v = w
  where
    w :: Term x -> Int
    w (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    w (LetTerm term binder body) = w term + if AnyVariable binder == AnyVariable v then 0 else w body
    w (LambdaTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else w body
    w (ApplyTerm f x) = w f + w x
    w _ = 0

inline :: Term a -> Builder Term a
inline = inline' VarMap.empty

data X a where
  X :: Builder Term a -> X a

inline' :: VarMap X -> Term a -> Builder Term a
inline' map = w
  where
    w :: Term x -> Builder Term x
    w (LetTerm term binder@(Variable t _) body) =
      let term' = w term
       in if count binder body <= 1 || isSimple term
            then inline' (VarMap.insert binder (X term') map) body
            else letBe term' $ \value ->
              inline' (VarMap.insert binder (X value) map) body
    w v@(VariableTerm variable) = case VarMap.lookup variable map of
      Just (X replacement) -> replacement
    w (ApplyTerm f x) = apply (w f) (w x)
    w (LambdaTerm binder@(Variable t _) body) = lambda t $ \value -> inline' (VarMap.insert binder (X value) map) body
    w (ConstantTerm c) = constant c
    w (GlobalTerm g) = global g

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple _ = False
