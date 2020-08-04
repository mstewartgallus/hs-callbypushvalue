{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsPorcelain (extract) where

import Common
import Constant
import Cps
import Data.Text
import HasConstants
import HasLet
import HasTuple
import TextShow
import qualified Unique

extract :: Data a -> Text
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

newtype Data (a :: Set) = D (Unique.State Builder)

newtype Code (a :: Algebra) = C (Unique.State Builder)

newtype Stack (a :: Algebra) = S (Unique.State Builder)

instance HasConstants Data where
  constant (U64Constant x) = D $ pure $ node $ atom "u64" <> ws <> showb x

instance HasTuple Code Data

instance HasLet Code Data

instance HasLabel Code Stack

instance HasThunk Code Data Stack where
  force (D th) (S k) = C $ do
    thunk' <- th
    k' <- k
    pure $ node $ atom "force" <> ws <> thunk' <> ws <> k'
  thunk t f = D $ do
    v <- fresh
    let C body = f (S $ pure v)
    body' <- body
    pure $ node $ atom "thunk" <> ws <> v <> ws <> pAction t <> ws <> body'

instance HasReturn Code Data Stack where
  returns (D value) (S k) = C $ do
    k' <- k
    value' <- value
    pure $ node $ atom "return" <> ws <> value' <> ws <> k'
  letTo t f = S $ do
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ node $ atom "to" <> ws <> v <> ws <> pType t <> ws <> body'

instance HasFn Code Data Stack where
  D h <*> S t = S $ do
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

instance HasCall Data where
  call g = D $ do
    pure $ node $ atom "call" <> ws <> showb g
