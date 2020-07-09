{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Code (..), Data (..), Builder (..), simplify, inline, typeOf) where

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

type Code = Data R

-- data Code where

data Data a where
  GlobalData :: Global a -> Data a
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  LetToData :: Variable a -> Code -> Data (Stack (F a))
  PushData :: Data a -> Data (Stack b) -> Data (Stack (a :=> b))
  ReturnCode :: Data a -> Data (Stack (F a)) -> Code
  PopCode :: Data (Stack (a :=> b)) -> Variable a -> Variable (Stack b) -> Code -> Code
  LetBeCode :: Data a -> Variable a -> Code -> Code

class Cps t where
  constant :: Constant a -> t a
  global :: Global a -> t a

  returns :: t a -> t (Stack (F a)) -> t R

  letBe :: t a -> (t a -> t R) -> t R

  pop :: t (Stack (a :=> b)) -> (t a -> t (Stack b) -> t R) -> t R

  letTo :: Type a -> (t a -> t R) -> t (Stack (F a))
  push :: t a -> t (Stack b) -> t (Stack (a :=> b))

instance Cps Builder where
  global g = (Builder . pure) $ GlobalData g
  returns value k =
    Builder $
      pure ReturnCode <*> builder value <*> builder k
  letBe x f = Builder $ do
    x' <- builder x
    let t = typeOfData x'
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) $ VariableData v)
    pure $ LetBeCode x' v body
  pop x f = Builder $ do
    x' <- builder x
    let StackType (a :=> b) = typeOfData x'
    h <- pure (Variable a) <*> Unique.uniqueId
    t <- pure (Variable (StackType b)) <*> Unique.uniqueId
    body <- builder $ f ((Builder . pure) (VariableData h)) ((Builder . pure) (VariableData t))
    pure $ PopCode x' h t body
  constant k = (Builder . pure) $ ConstantData k

  letTo t f = Builder $ do
    v <- pure (Variable t) <*> Unique.uniqueId
    body <- builder (f ((Builder . pure) $ VariableData v))
    pure $ LetToData v body

  push x k = Builder $ do
    pure PushData <*> builder x <*> builder k

instance TextShow (Data a) where
  showb (ReturnCode x k) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb x))) <> fromString "\n}\n" <> showb k
  showb (PopCode value h t body) = showb value <> fromString " pop (" <> showb h <> fromString ", " <> showb t <> fromString ").\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (GlobalData k) = showb k
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (LetToData binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body
  showb (PushData x f) = showb x <> fromString " :: " <> showb f

build :: Builder a -> Data a
build (Builder s) = Unique.run s

newtype Builder a = Builder {builder :: Unique.State (Data a)}

typeOf :: Code -> Action R
typeOf _ = R

typeOfData :: Data a -> Type a
typeOfData (GlobalData (Global t _)) = t
typeOfData (ConstantData k) = Constant.typeOf k
typeOfData (VariableData (Variable t _)) = t
typeOfData (LetToData (Variable t _) _) = StackType (F t)
typeOfData (PushData h t) =
  let a = typeOfData h
      StackType b = typeOfData t
   in StackType (a :=> b)

simplify :: Data a -> Data a
simplify = simpData

simpData :: Data a -> Data a
simpData (LetToData binder body) = LetToData binder (simpCode body)
simpData (PushData h t) = PushData (simpData h) (simpData t)
simpData x = x

simpCode :: Code -> Code
simpCode (PopCode value h t body) = PopCode (simpData value) h t (simpCode body)
simpCode (LetBeCode thing binder body) = LetBeCode (simpData thing) binder (simpCode body)
simpCode (ReturnCode value k) = ReturnCode (simpData value) (simpData k)

inline :: Cps t => Data a -> t a
inline = inlineData VarMap.empty

newtype X t a = X (t a)

inlineData :: Cps t => VarMap (X t) -> Data a -> t a
inlineData env (VariableData v) =
  let Just (X x) = VarMap.lookup v env
   in x
inlineData env (LetToData binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder (X value) env
   in inlineCode env' body
inlineData env (PushData h t) = Cps.push (inlineData env h) (inlineData env t)
inlineData _ (ConstantData k) = Cps.constant k
inlineData _ (GlobalData g) = global g

isSimple :: Data a -> Bool
isSimple (ConstantData _) = True
isSimple (VariableData _) = True
isSimple (GlobalData _) = True
isSimple _ = False

inlineCode :: Cps t => VarMap (X t) -> Code -> t R
inlineCode env (LetBeCode term binder body)
  | count binder body <= 1 || isSimple term =
    let term' = inlineData env term
     in inlineCode (VarMap.insert binder (X term') env) body
  | otherwise = letBe (inlineData env term) $ \x ->
    inlineCode (VarMap.insert binder (X x) env) body
inlineCode env (PopCode value h t body) = pop (inlineData env value) $ \x y ->
  inlineCode (VarMap.insert t (X y) (VarMap.insert h (X x) env)) body
inlineCode env (ReturnCode val k) = returns (inlineData env val) (inlineData env k)

count :: Variable a -> Code -> Int
count v = code
  where
    code :: Code -> Int
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (PopCode x h t body) = value x + if AnyVariable t == AnyVariable v || AnyVariable h == AnyVariable v then 0 else code body
    code (ReturnCode x k) = value x + value k
    code _ = 0
    value :: Data x -> Int
    value (LetToData binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    value (PushData h t) = value h + value t
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0
