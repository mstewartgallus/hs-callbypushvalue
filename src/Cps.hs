{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Term (..), Builder (..), simplify, inline, typeOf) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Global
import TextShow (TextShow, fromString, fromText, showb, toText)
import Type
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

data Term a where
  GlobalTerm :: Global a -> Term a
  ConstantTerm :: Constant a -> Term a
  VariableTerm :: Variable a -> Term a
  LetToTerm :: Variable a -> Term R -> Term (Stack (F a))
  PushTerm :: Term a -> Term (Stack b) -> Term (Stack (a :=> b))
  ReturnCode :: Term a -> Term (Stack (F a)) -> Term R
  PopCode :: Term (Stack (a :=> b)) -> Variable a -> Variable (Stack b) -> Term R -> Term R
  LetBeCode :: Term a -> Variable a -> Term R -> Term R

class Cps t where
  constant :: Constant a -> t a
  global :: Global a -> t a

  returns :: t a -> t (Stack (F a)) -> t R

  letBe :: t a -> (t a -> t R) -> t R

  pop :: t (Stack (a :=> b)) -> (t a -> t (Stack b) -> t R) -> t R

  letTo :: Type a -> (t a -> t R) -> t (Stack (F a))
  push :: t a -> t (Stack b) -> t (Stack (a :=> b))

instance Cps Builder where
  global g = (Builder . pure) $ GlobalTerm g
  returns value k =
    Builder $
      pure ReturnCode <*> builder value <*> builder k
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOf x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableTerm v)
    pure $ LetBeCode x' v body
  pop x f = Builder $ do
    x' <- builder x
    let StackType (a :=> b) = typeOf x'
    h <- pure (Variable a) <*> Unique.uniqueId
    t <- pure (Variable (StackType b)) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) (VariableTerm h)) ((Builder . pure) (VariableTerm t))
    pure $ PopCode x' h t body
  constant k = (Builder . pure) $ ConstantTerm k

  letTo t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableTerm v))
    pure $ LetToTerm v body

  push x k = Builder $ do
    pure PushTerm <*> builder x <*> builder k

instance TextShow (Term a) where
  showb (ReturnCode x k) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb x))) <> fromString "\n}\n" <> showb k
  showb (PopCode value h t body) = showb value <> fromString " pop (" <> showb h <> fromString ", " <> showb t <> fromString ").\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (GlobalTerm k) = showb k
  showb (ConstantTerm k) = showb k
  showb (VariableTerm v) = showb v
  showb (LetToTerm binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body
  showb (PushTerm x f) = showb x <> fromString " :: " <> showb f

build :: Builder a -> Term a
build (Builder s) = Unique.run s

newtype Builder a = Builder {builder :: Unique.State (Term a)}

typeOf :: Term a -> Type a
typeOf (GlobalTerm (Global t _)) = t
typeOf (ConstantTerm k) = Constant.typeOf k
typeOf (VariableTerm (Variable t _)) = t
typeOf (LetToTerm (Variable t _) _) = StackType (F t)
typeOf (PushTerm h t) =
  let a = typeOf h
      StackType b = typeOf t
   in StackType (a :=> b)

simplify :: Term a -> Term a
simplify (LetToTerm binder body) = LetToTerm binder (simplify body)
simplify (PushTerm h t) = PushTerm (simplify h) (simplify t)
simplify (PopCode value h t body) = PopCode (simplify value) h t (simplify body)
simplify (LetBeCode thing binder body) = LetBeCode (simplify thing) binder (simplify body)
simplify (ReturnCode value k) = ReturnCode (simplify value) (simplify k)
simplify x = x

inline :: Cps t => Term a -> t a
inline = inline' VarMap.empty

newtype X t a = X (t a)

inline' :: Cps t => VarMap (X t) -> Term a -> t a
inline' env (VariableTerm v) =
  let Just (X x) = VarMap.lookup v env
   in x
inline' env (LetToTerm binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in inline' env' body
inline' env (PushTerm h t) = Cps.push (inline' env h) (inline' env t)
inline' _ (ConstantTerm k) = Cps.constant k
inline' _ (GlobalTerm g) = global g
inline' env (LetBeCode term binder body)
  | count binder body <= 1 || isSimple term =
    let term' = inline' env term
     in inline' (VarMap.insert binder (X term') env) body
  | otherwise = letBe (inline' env term) $ \x ->
    inline' (VarMap.insert binder (X x) env) body
inline' env (PopCode value h t body) = pop (inline' env value) $ \x y ->
  inline' (VarMap.insert t (X y) (VarMap.insert h (X x) env)) body
inline' env (ReturnCode val k) = returns (inline' env val) (inline' env k)

isSimple :: Term a -> Bool
isSimple (ConstantTerm _) = True
isSimple (VariableTerm _) = True
isSimple (GlobalTerm _) = True
isSimple _ = False

count :: Variable a -> Term b -> Int
count v = w
  where
    w :: Term b -> Int
    w (LetBeCode x binder body) = w x + if AnyVariable binder == AnyVariable v then 0 else w body
    w (PopCode x h t body) = w x + if AnyVariable t == AnyVariable v || AnyVariable h == AnyVariable v then 0 else w body
    w (ReturnCode x k) = w x + w k
    w (LetToTerm binder body) = if AnyVariable binder == AnyVariable v then 0 else w body
    w (PushTerm h t) = w h + w t
    w (VariableTerm binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    w _ = 0
