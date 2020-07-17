{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsPorcelain (Porcelain, extract) where

import Common
import Constant
import Core
import qualified Cps
import Data.Text
import HasCode
import HasConstants
import HasData
import HasLet
import HasLetLabel
import HasStack
import HasThunk
import TextShow
import Tuple
import qualified Unique

extract :: DataRep Porcelain a -> Text
extract (XD val) = toText (Unique.run val)

ws = fromString " "

lp = fromString "("

rp = fromString ")"

atom = fromString

node x = lp <> x <> rp

fresh = do
  v <- Unique.uniqueId
  pure $ fromString "v" <> showb v

pType :: SSet a -> Builder
pType = showb

pAction :: SAlgebra a -> Builder
pAction = showb

data Porcelain

instance HasData Porcelain where
  newtype DataRep Porcelain a = XD (Unique.State Builder)

instance HasCode Porcelain where
  newtype CodeRep Porcelain a = XC (Unique.State Builder)

instance HasStack Porcelain where
  newtype StackRep Porcelain a = XS (Unique.State Builder)

instance HasConstants Porcelain where
  constant (U64Constant x) = XD $ pure $ node $ atom "u64" <> ws <> showb x

instance Tuple Porcelain

instance HasLet Porcelain

instance HasLetLabel Porcelain

instance HasThunk Porcelain where
  force (XD thunk) (XS k) = XC $ do
    thunk' <- thunk
    k' <- k
    pure $ node $ atom "force" <> ws <> thunk' <> ws <> k'
  thunk t f = XD $ do
    v <- fresh
    let XC body = f (XS $ pure v)
    body' <- body
    pure $ node $ atom "thunk" <> ws <> v <> ws <> pAction t <> ws <> body'
  lambda (XS k) f = XC $ do
    k' <- k
    x <- fresh
    t <- fresh
    let XC body = f (XD $ pure x) (XS $ pure t)
    body' <- body
    pure $ node $ atom "lambda" <> ws <> k' <> ws <> x <> ws <> t <> ws <> body'
  call g (XS k) = XC $ do
    k' <- k
    pure $ node $ atom "call" <> ws <> showb g <> ws <> k'

instance Cps.Cps Porcelain where
  throw (XS k) (XD value) = XC $ do
    k' <- k
    value' <- value
    pure $ node $ atom "throw" <> ws <> k' <> ws <> value'

  letTo t f = XS $ do
    v <- fresh
    let XC body = f (XD $ pure v)
    body' <- body
    pure $ node $ atom "to" <> ws <> v <> ws <> pType t <> ws <> body'

  apply (XD h) (XS t) = XS $ do
    h' <- h
    t' <- t
    pure $ node $ atom "apply" <> ws <> h' <> ws <> t'

  nil = XS $ pure $ atom "nil"
