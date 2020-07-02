{-# LANGUAGE GADTs, TypeOperators, StandaloneDeriving #-}
module Cps (Cps (..), Stuff (..), Effect (..)) where
import Common
import TextShow
import qualified Data.Text as T
import VarMap (VarMap)
import qualified VarMap

data Cps a where
  GlobalCps :: Global a -> Cps a
  ApplyCps :: Cps (a -> b) -> Stuff a -> Cps b
  ReturnCps :: Stuff a -> Cps (F a)
  LabelCps :: Label a -> Cps a
  LambdaCps :: Variable (Stack b) -> Stuff (Stack (F a)) -> Cps (a -> b)

data Stuff a where
  ConstantStuff :: Constant a -> Stuff a
  VariableStuff :: Variable a -> Stuff a
  ToStackStuff :: Variable a -> Effect -> Stuff (Stack (F a))
  LabelStackStuff :: Label a -> Effect -> Stuff (Stack a)

data Effect where
  JumpEffect :: Cps a -> Stuff (Stack a) -> Effect

instance TextShow (Cps a) where
  showb (GlobalCps k) = showb k
  showb (ApplyCps f x) = showb x <> fromString "\n" <> showb f
  showb (ReturnCps x) = fromString "return " <> showb x
  showb (LabelCps l) = showb l
  showb (LambdaCps k body) = fromString "κ " <> showb k <> fromString " →\n" <> showb body

instance TextShow (Stuff a) where
 showb (ConstantStuff k) = showb k
 showb (VariableStuff v) = showb v
 showb (ToStackStuff binder effect) = fromString "to " <> showb binder <> fromString ".\n" <> showb effect
 showb (LabelStackStuff binder effect) = fromString "κ " <> showb binder <> fromString " →\n" <> showb effect

instance TextShow Effect where
 showb (JumpEffect action stack) = fromString "{" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb action))) <> fromString "\n}\n" <> showb stack

newtype Id a = Id a

interpretStuff :: VarMap Id -> Stuff a -> a
interpretStuff _ (ConstantStuff k) = interpretConstant k
interpretStuff values (VariableStuff v) = case VarMap.lookup v values of
  Just (Id x) -> x
interpretStuff values (ToStackStuff variable effect) = PopStack $ \value -> interpretEffect (VarMap.insert variable (Id value) values) effect

interpret :: VarMap Id -> Cps a -> Stack a -> IO ()
interpret values (ReturnCps value) (PopStack k) = let
  value' = interpretStuff values value
  in k value'
interpret values (LambdaCps variable body) (PushStack head tail) = let
  values' = VarMap.insert variable (Id tail) values
  PopStack body' = interpretStuff values' body
  in body' head
-- interpret values (LabelCps label) (PopStack k) = let
--   value' = interpretStuff values value
--   in k value'

interpretEffect :: VarMap Id -> Effect -> IO ()
interpretEffect values (JumpEffect ip stack) = let
  stack' = interpretStuff values stack
  in interpret values ip stack'

interpretConstant :: Constant a -> a
interpretConstant (IntegerConstant x) = x
