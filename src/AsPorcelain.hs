{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsPorcelain (Porcelain, extract) where

import Common
import Constant
import qualified Cps
import Data.Text
import HasCode
import HasConstants
import HasCpsReturn
import HasCpsThunk
import HasData
import HasLet
import HasLetLabel
import HasStack
import HasTuple
import TextShow
import qualified Unique

extract :: Data Porcelain a -> Text
extract (D val) = toText (Unique.run val)

ws :: Builder
ws = fromString " "

lp :: Builder
lp = fromString "("

rp :: Builder
rp = fromString ")"

atom :: String -> Builder
atom = fromString

node :: Builder -> Builder
node x = lp <> x <> rp

fresh :: Unique.State Builder
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
  unit = D $ pure $ atom "unit"
  constant (U64Constant x) = D $ pure $ node $ atom "u64" <> ws <> showb x

instance HasTuple Porcelain

instance HasLet Porcelain

instance HasLetLabel Porcelain

instance HasCpsThunk Porcelain where
  force (D th) (S k) = C $ do
    thunk' <- th
    k' <- k
    pure $ node $ atom "force" <> ws <> thunk' <> ws <> k'
  thunk t f = D $ do
    v <- fresh
    let C body = f (S $ pure v)
    body' <- body
    pure $ node $ atom "thunk" <> ws <> v <> ws <> pAction t <> ws <> body'

instance HasCpsReturn Porcelain where
  returns (S k) (D value) = C $ do
    k' <- k
    value' <- value
    pure $ node $ atom "return" <> ws <> k' <> ws <> value'
  letTo t f = S $ do
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ node $ atom "to" <> ws <> v <> ws <> pType t <> ws <> body'

instance Cps.Cps Porcelain where
  apply (D h) (S t) = S $ do
    h' <- h
    t' <- t
    pure $ node $ atom "apply" <> ws <> h' <> ws <> t'
  lambda (S k) f = C $ do
    k' <- k
    x <- fresh
    n <- fresh
    let C body = f (D $ pure x) (S $ pure n)
    body' <- body
    pure $ node $ atom "lambda" <> ws <> k' <> ws <> x <> ws <> n <> ws <> body'
  nil = S $ pure $ atom "nil"
  call g (S k) = C $ do
    k' <- k
    pure $ node $ atom "call" <> ws <> showb g <> ws <> k'
