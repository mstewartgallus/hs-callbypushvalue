{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Porcelain (porcelain) where

import Common
import Constant
import Core
import qualified Cps
import Data.Text
import GlobalMap (GlobalMap)
import qualified GlobalMap
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow
import Type
import qualified Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

porcelain :: Cps.Data a -> Text
porcelain x = toText (Unique.run (build (Cps.abstract x)))

newtype X a = X {build :: Unique.State Builder}

ws = fromString " "

lp = fromString "("

rp = fromString ")"

atom = fromString

node x = lp <> x <> rp

fresh = do
  v <- Unique.uniqueId
  pure $ fromString "v" <> showb v

pType :: Type a -> Builder
pType = showb

pAction :: Action a -> Builder
pAction = showb

instance Cps.Cps X where
  throw (X k) (X value) = X $ do
    k' <- k
    value' <- value
    pure $ node $ atom "throw" <> ws <> k' <> ws <> value'
  force (X thunk) (X k) = X $ do
    thunk' <- thunk
    k' <- k
    pure $ node $ atom "force" <> ws <> thunk' <> ws <> k'

  thunk t f = X $ do
    v <- fresh
    body <- build (f (X $ pure v))
    pure $ node $ atom "thunk" <> ws <> v <> ws <> pAction t <> ws <> body
  letTo t f = X $ do
    v <- fresh
    body <- build (f (X $ pure v))
    pure $ node $ atom "to" <> ws <> v <> ws <> pType t <> ws <> body

  lambda t a f = X $ do
    x <- fresh
    k <- fresh
    body <- build (f (X $ pure x) (X $ pure k))
    pure $ node $ atom "lambda" <> ws <> x <> ws <> pType t <> ws <> k <> ws <> pAction a <> ws <> body
  push (X h) (X t) = X $ do
    h' <- h
    t' <- t
    pure $ node $ atom "push" <> ws <> h' <> ws <> t'

  nilStack = X $ pure $ atom "nil"
  global g (X k) = X $ do
    k' <- k
    pure $ node $ atom "global" <> ws <> showb g <> ws <> k'
  constant (IntegerConstant x) = X $ pure $ node $ atom "int" <> ws <> showb x
