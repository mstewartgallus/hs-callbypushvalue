{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Interpreter (evaluate) where

import Common
import Constant
import Core
import Cps
import GlobalMap (GlobalMap)
import qualified GlobalMap
import VarMap (VarMap)
import qualified VarMap

evaluate :: Data a -> a
evaluate = interpretData VarMap.empty

newtype Id a = Id a

interpretData :: VarMap Id -> Data a -> a
interpretData _ (ConstantData k) = interpretConstant k
interpretData env (VariableData v) = case VarMap.lookup v env of
  Just (Id x) -> x
  Nothing -> error "variable not found in environment"
interpretData env (LetToData binder body) = PopStack $ \value ->
  let env' = VarMap.insert binder (Id value) env
   in interpret env' body NilStack
interpretData env (PushData h t) =
  let h' = interpretData env h
      t' = interpretData env t
   in PushStack h' t'
interpretData _ NilStackData = NilStack

interpret :: VarMap Id -> Code a -> Stack a -> R
interpret env (ReturnCode value) (PopStack k) =
  let value' = interpretData env value
   in k value'
interpret env (LetBeCode value binder body) k =
  let value' = interpretData env value
      env' = VarMap.insert binder (Id value') env
   in interpret env' body k
interpret env (LambdaCode variable body) (PushStack h t) =
  let env' = VarMap.insert variable (Id h) env
   in interpret env' body t
interpret _ (GlobalCode g) k =
  let Just (X g') = GlobalMap.lookup g globals
   in g' k
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
