{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsPorcelain (Porcelain, extract) where

import Common
import Constant
import Cps
import Data.Text
import HasCode
import HasConstants
import HasData
import HasLet
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

node :: [Builder] -> Builder
node x = lp <> mconcat (interleave ws x) <> rp

interleave :: a -> [a] -> [a]
interleave x = w
  where
    w [] = []
    w l@[_] = l
    w (h : t) = h : x : w t

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
  constant (U64Constant x) = D $ pure $ node [atom "u64", showb x]

instance HasTuple Porcelain where
  pair (D x) (D y) = D $ do
    x' <- x
    y' <- y
    pure $ node [atom "pair", x', y']
  unpair (D t) f = C $ do
    t' <- t
    x <- fresh
    y <- fresh
    let C body = f (D $ pure x) (D $ pure y)
    body' <- body
    pure $ node [atom "unpair", t', x, y, body']

instance HasLet Porcelain where
  letBe (D x) f = C $ do
    x' <- x
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ node [atom "be", x', body']

instance HasLabel Porcelain where
  label (S x) f = C $ do
    x' <- x
    v <- fresh
    let C body = f (S $ pure v)
    body' <- body
    pure $ node [atom "label", x', body']

instance HasThunk Porcelain where
  force (D th) (S k) = C $ do
    thunk' <- th
    k' <- k
    pure $ node [atom "force", thunk', k']
  thunk t f = D $ do
    v <- fresh
    let C body = f (S $ pure v)
    body' <- body
    pure $ node [atom "thunk", v, pAction t, body']

instance HasReturn Porcelain where
  returns (D value) (S k) = C $ do
    k' <- k
    value' <- value
    pure $ node [atom "return", value', k']
  letTo t f = S $ do
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ node [atom "to", v, pType t, body']

instance HasFn Porcelain where
  D h <*> S t = S $ do
    h' <- h
    t' <- t
    pure $ node [atom "apply", h', t']
  lambda (S k) f = C $ do
    k' <- k
    x <- fresh
    n <- fresh
    let C body = f (D $ pure x) (S $ pure n)
    body' <- body
    pure $ node [atom "lambda", k', x, n, body']

instance HasCall Porcelain where
  call g = D $ do
    pure $ node [atom "call", showb g]
