{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module SystemF (simplify, inline, build, Builder, SystemF (..), Term (..)) where

import Common
import Core
import TextShow (TextShow, fromString, showb)
import qualified Unique
import VarMap (VarMap)
import qualified VarMap

class SystemF t where
  constant :: Constant a -> t (F a)
  global :: Global a -> t a
  lambda :: Type a -> (t a -> t b) -> t (a :-> b)
  apply :: t (a :-> b) -> t a -> t b
  letBe :: t a -> (t a -> t b) -> t b

newtype Builder a = Builder {build :: Unique.Stream -> Term a}

instance SystemF Builder where
  constant k = (Builder . const) $ ConstantTerm k
  global g = (Builder . const) $ GlobalTerm g
  letBe value f = Builder $ \(Unique.Pick head (Unique.Split l r)) ->
    let value' = build value l
        t = typeOf value'
        binder = Variable t head
        body = build (f (Builder $ const $ VariableTerm binder)) r
     in LetTerm value' binder body
  lambda t f = Builder $ \(Unique.Pick h stream) ->
    let binder = Variable t h
        body = build (f (Builder $ const $ VariableTerm binder)) stream
     in LambdaTerm binder body
  apply f x = Builder $ \(Unique.Split l r) ->
    let f' = build f l
        x' = build x r
     in ApplyTerm f' x'

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
typeOf (LambdaTerm (Variable t _) body) = ApplyType thunk t -=> typeOf body
typeOf (ApplyTerm f _) =
  let _ :=> result = typeOf f
   in result

instance TextShow (Term a) where
  showb (VariableTerm v) = showb v
  showb (ConstantTerm k) = showb k
  showb (GlobalTerm g) = showb g
  showb (LetTerm term binder body) = showb term <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (LambdaTerm binder body) = fromString "λ " <> showb binder <> fromString " →\n" <> showb body
  showb (ApplyTerm f x) = showb x <> fromString "\n" <> showb f

simplify :: Term a -> Builder a
simplify = simplify' VarMap.empty

simplify' :: VarMap X -> Term a -> Builder a
simplify' map = loop
  where
    loop :: Term x -> Builder x
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

inline :: Term a -> Builder a
inline = inline' VarMap.empty

data X a where
  X :: Builder a -> X a

inline' :: VarMap X -> Term a -> Builder a
inline' map = w
  where
    w :: Term x -> Builder x
    w (LetTerm term binder@(Variable t _) body) =
      let term' = w term
       in if count binder body <= 1
            then inline' (VarMap.insert binder (X term') map) body
            else letBe term' $ \value ->
              inline' (VarMap.insert binder (X value) map) body
    w v@(VariableTerm variable) = case VarMap.lookup variable map of
      Just (X replacement) -> replacement
    w (ApplyTerm f x) = apply (w f) (w x)
    w (LambdaTerm binder@(Variable t _) body) = lambda t $ \value -> inline' (VarMap.insert binder (X value) map) body
    w (ConstantTerm c) = constant c
    w (GlobalTerm g) = global g
