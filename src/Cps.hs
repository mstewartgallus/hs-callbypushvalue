{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Code (..), Data (..), Builder (..), simplify, inline, typeOf) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import Global
import TextShow (TextShow, fromString, showb)
import Type (Type)
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

data Code a where
  ReturnCode :: Data a -> Data (Stack (F a)) -> Code Nil
  JumpCode :: Code a -> Data (Stack a) -> Code Nil
  PopCode :: Data (Stack (a -> b)) -> Variable a -> Variable (Stack b) -> Code c -> Code c
  LetBeCode :: Data a -> Variable a -> Code b -> Code b

data Data a where
  GlobalData :: Global a -> Data a
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  LetToData :: Variable a -> Code Nil -> Data (Stack (F a))
  PushData :: Data a -> Data (Stack b) -> Data (Stack (a -> b))
  NilStackData :: Data (Stack Nil)

class Cps t where
  constant :: Constant a -> t Data a
  global :: Global a -> t Data a

  returns :: t Data a -> t Data (Stack (F a)) -> t Code Nil

  letBe :: t Data a -> (t Data a -> t Code b) -> t Code b

  pop :: t Data (Stack (a -> b)) -> (t Data a -> t Data (Stack b) -> t Code c) -> t Code c
  jump :: t Code a -> t Data (Stack a) -> t Code Nil

  letTo :: Type a -> (t Data a -> t Code Nil) -> t Data (Stack (F a))
  push :: t Data a -> t Data (Stack b) -> t Data (Stack (a -> b))

  nilStack :: t Data (Stack Nil)

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

  jump x f =
    Builder $
      pure JumpCode <*> builder x <*> builder f

  nilStack = Builder $ pure $ NilStackData
  push x k = Builder $ do
    pure PushData <*> builder x <*> builder k

instance TextShow (Code a) where
  showb (ReturnCode x k) = fromString "return " <> showb x <> fromString ".\n" <> showb k
  showb (PopCode value h t body) = showb value <> fromString " pop (" <> showb h <> fromString ", " <> showb t <> fromString ").\n" <> showb body
  showb (LetBeCode value binder body) = showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
  showb (JumpCode action stack) = showb action <> fromString " , " <> showb stack

instance TextShow (Data a) where
  showb NilStackData = fromString "nil"
  showb (GlobalData k) = showb k
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (LetToData binder body) = fromString "to " <> showb binder <> fromString ".\n" <> showb body
  showb (PushData x f) = showb x <> fromString " :: " <> showb f

build :: Builder t a -> t a
build (Builder s) = Unique.run s

newtype Builder t a = Builder {builder :: Unique.State (t a)}

typeOf :: Code a -> Type a
typeOf (PopCode _ _ _ body) = typeOf body
typeOf (LetBeCode _ _ body) = typeOf body
typeOf (ReturnCode _ _) = NilType
typeOf (JumpCode _ _) = NilType

typeOfData :: Data a -> Type a
typeOfData (GlobalData (Global t _)) = t
typeOfData (ConstantData k) = Constant.typeOf k
typeOfData (VariableData (Variable t _)) = t
typeOfData (LetToData (Variable t _) _) = StackType (F t)
typeOfData (PushData h t) =
  let a = typeOfData h
      StackType b = typeOfData t
   in StackType (a :=> b)
typeOfData NilStackData = StackType NilType

simplify :: Data a -> Data a
simplify = simpData

simpData :: Data a -> Data a
simpData (LetToData binder body) = LetToData binder (simpCode body)
simpData (PushData h t) = PushData (simpData h) (simpData t)
simpData x = x

simpCode :: Code a -> Code a
simpCode (PopCode value h t body) = PopCode (simpData value) h t (simpCode body)
simpCode (LetBeCode thing binder body) = LetBeCode (simpData thing) binder (simpCode body)
simpCode (JumpCode x f) = JumpCode (simpCode x) (simpData f)
simpCode (ReturnCode value k) = ReturnCode (simpData value) (simpData k)

inline :: Data a -> Builder Data a
inline = inlineData VarMap.empty

inlineData :: Cps t => VarMap (t Data) -> Data a -> t Data a
inlineData env (VariableData v) =
  let Just x = VarMap.lookup v env
   in x
inlineData env (LetToData binder@(Variable t _) body) = Cps.letTo t $ \value ->
  let env' = VarMap.insert binder value env
   in inlineCode env' body
inlineData env (PushData h t) = Cps.push (inlineData env h) (inlineData env t)
inlineData _ (ConstantData k) = Cps.constant k
inlineData _ (GlobalData g) = global g
inlineData _ NilStackData = Cps.nilStack

inlineCode :: Cps t => VarMap (t Data) -> Code x -> t Code x
inlineCode env (LetBeCode term binder body) =
  let term' = inlineData env term
   in if count binder body <= 1
        then inlineCode (VarMap.insert binder term' env) body
        else letBe term' $ \x ->
          inlineCode (VarMap.insert binder x env) body
inlineCode env (PopCode value h t body) = pop (inlineData env value) $ \x y ->
  inlineCode (VarMap.insert t y (VarMap.insert h x env)) body
inlineCode env (ReturnCode val k) = returns (inlineData env val) (inlineData env k)
inlineCode env (JumpCode x f) = jump (inlineCode env x) (inlineData env f)

count :: Variable a -> Code b -> Int
count v = code
  where
    code :: Code x -> Int
    code (JumpCode x f) = code x + value f
    code (LetBeCode x binder body) = value x + if AnyVariable binder == AnyVariable v then 0 else code body
    code (PopCode x h t body) = value x + if AnyVariable t == AnyVariable v || AnyVariable h == AnyVariable v then 0 else code body
    code (ReturnCode x k) = value x + value k
    code _ = 0
    value :: Data x -> Int
    value (LetToData binder body) = if AnyVariable binder == AnyVariable v then 0 else code body
    value (PushData h t) = value h + value t
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value _ = 0
