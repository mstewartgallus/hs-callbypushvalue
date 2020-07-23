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
import HasTuple
import TextShow
import qualified Unique

extract :: Data Porcelain a -> Text
extract (D val) = toText (Unique.run val)

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
  newtype Data Porcelain a = D (Unique.State Builder)

instance HasCode Porcelain where
  newtype Code Porcelain a = C (Unique.State Builder)

instance HasStack Porcelain where
  newtype Stack Porcelain a = S (Unique.State Builder)

instance HasConstants Porcelain where
  constant (U64Constant x) = D $ pure $ node $ atom "u64" <> ws <> showb x

instance HasTuple Porcelain

instance HasLet Porcelain

instance HasLetLabel Porcelain

instance HasThunk Porcelain where
  force (D thunk) (S k) = C $ do
    thunk' <- thunk
    k' <- k
    pure $ node $ atom "force" <> ws <> thunk' <> ws <> k'
  thunk t f = D $ do
    v <- fresh
    let C body = f (S $ pure v)
    body' <- body
    pure $ node $ atom "thunk" <> ws <> v <> ws <> pAction t <> ws <> body'
  lambda (S k) f = C $ do
    k' <- k
    x <- fresh
    t <- fresh
    let C body = f (D $ pure x) (S $ pure t)
    body' <- body
    pure $ node $ atom "lambda" <> ws <> k' <> ws <> x <> ws <> t <> ws <> body'
  call g (S k) = C $ do
    k' <- k
    pure $ node $ atom "call" <> ws <> showb g <> ws <> k'

instance Cps.Cps Porcelain where
  throw (S k) (D value) = C $ do
    k' <- k
    value' <- value
    pure $ node $ atom "throw" <> ws <> k' <> ws <> value'

  letTo t f = S $ do
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ node $ atom "to" <> ws <> v <> ws <> pType t <> ws <> body'

  apply (D h) (S t) = S $ do
    h' <- h
    t' <- t
    pure $ node $ atom "apply" <> ws <> h' <> ws <> t'

  nil = S $ pure $ atom "nil"
