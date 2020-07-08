{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (evaluate) where

import Common
import Constant
import Core
import Cps
import qualified Data.Text as T
import Global
import GlobalMap (GlobalMap)
import qualified GlobalMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Type
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

evaluate :: Data a -> a
evaluate = interpretData VarMap.empty

newtype Id a = Id a

interpretData :: VarMap Id -> Data a -> a
interpretData _ (ConstantData k) = interpretConstant k
interpretData env (VariableData v) = case VarMap.lookup v env of
  Just (Id x) -> x
interpretData env (LetToData binder body) = PopStack $ \value ->
  let env' = VarMap.insert binder (Id value) env
   in interpret env' body NilStack
interpretData env (PushData h t) =
  let h' = interpretData env h
      t' = interpretData env t
   in PushStack h' t'

interpret :: VarMap Id -> Code a -> Stack a -> R
interpret values (ReturnCode value) (PopStack k) =
  let value' = interpretData values value
   in k value'
interpret env (LetBeCode value binder body) k =
  let value' = interpretData env value
      env' = VarMap.insert binder (Id value') env
   in interpret env' body k
interpret values (LambdaCode variable body) (PushStack head tail) =
  let values' = VarMap.insert variable (Id head) values
   in interpret values' body tail
interpret values (GlobalCode global) k =
  let Just (X g) = GlobalMap.lookup global globals
   in g k
interpret env (JumpCode x f) NilStack =
  let stack = interpretData env f
   in interpret env x stack

data X a = X (Stack a -> R)

globals :: GlobalMap X
globals =
  GlobalMap.fromList
    [ GlobalMap.Entry strictPlus (X strictPlusImpl)
    ]

strictPlusImpl :: Stack (Integer -> Integer -> F Integer) -> R
strictPlusImpl (PushStack x (PushStack y (PopStack k))) = k (x + y)

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
