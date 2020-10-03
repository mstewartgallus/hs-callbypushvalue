{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module AsText (extract, extractData, AsText) where

import Cbpv
import qualified Cps
import qualified Data.Text as T
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTerminal
import HasTuple
import qualified SystemF
import TextShow
import qualified Unique

data AsText

extract :: Code AsText a -> T.Text
extract (C x) = toText (Unique.run x)

extractData :: Data AsText a -> T.Text
extractData (D x) = toText (Unique.run x)

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

freshLabel :: Unique.State Builder
freshLabel = do
  v <- Unique.uniqueId
  pure $ fromString "l" <> showb v

instance HasData AsText where
  newtype Data AsText a = D (Unique.State Builder)

instance HasCode AsText where
  newtype Code AsText a = C (Unique.State Builder)

instance HasStack AsText where
  newtype Stack AsText a = S (Unique.State Builder)

instance SystemF.HasLet AsText where
  letBe (C x) f = C $ do
    x' <- x
    newId <- fresh
    let binder = fromString "l" <> showb newId
    let C y = f (C $ pure binder)
    y' <- y
    pure $ x' <> fromString " be " <> binder <> fromString ".\n" <> y'

instance Cps.HasLabel AsText where
  label (S x) f = C $ do
    x' <- x
    v <- fresh
    let C body = f (S $ pure v)
    body' <- body
    pure $ node [atom "label", x', body']

instance HasReturn AsText where
  returns (D value) = C $ do
    value' <- value
    pure $ fromString "return " <> value'
  letTo (C x) f = C $ do
    x' <- x
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ x' <> fromString " to " <> v <> fromString ".\n" <> body'

instance HasCall AsText where
  call g = C $ do
    pure $ fromString "call " <> showb g

instance SystemF.HasConstants AsText where
  constant k = C $ pure $ showb k

instance HasConstants AsText where
  constant k = D $ pure $ showb k

instance HasTerminal AsText where
  terminal = D $ pure $ atom "{}"

instance HasTuple AsText where
  first (D tuple) = D $ do
    tuple' <- tuple
    pure $ tuple' <> fromString ".1"
  second (D tuple) = D $ do
    tuple' <- tuple
    pure $ tuple' <> fromString ".2"

instance SystemF.HasTuple AsText where
  -- pair (C x) (C y) = C $ \(Unique.Stream _ xs ys) ->
  --   let x' = x xs
  --       y' = y ys
  --    in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"

  first (C tuple) = C $ do
    tuple' <- tuple
    pure $ tuple' <> fromString ".1"
  second (C tuple) = C $ do
    tuple' <- tuple
    pure $ tuple' <> fromString ".2"

instance SystemF.HasFn AsText where
  lambda t f = C $ do
    binder <- fresh
    let C y = f (C $ pure binder)
    y' <- y
    pure $ fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> y'
  C f <*> C x = C $ do
    f' <- f
    x' <- x
    pure $ fromString "(" <> f' <> fromString " " <> x' <> fromString ")"

instance HasLet AsText where
  letBe (D x) f = C $ do
    x' <- x
    v <- fresh
    let C body = f (D $ pure v)
    body' <- body
    pure $ x' <> fromString " be " <> v <> fromString ".\n" <> body'

instance HasFn AsText where
  C h <*> D t = C $ do
    h' <- h
    t' <- t
    pure $ h' <> fromString "\n" <> t'
  lambda t f = C $ do
    x <- fresh
    let C body = f (D $ pure x)
    body' <- body
    pure $ fromString "λ " <> x <> fromString ": " <> showb t <> fromString "→\n" <> body'

instance HasThunk AsText where
  force (D th) = C $ do
    thunk' <- th
    pure $ fromString "! " <> thunk'
  thunk (C x) = D $ do
    x' <- x
    pure $ fromString "thunk {" <> indent (fromString "\n" <> x') <> fromString "}"

indent :: Builder -> Builder
indent = fromText . T.unlines . fmap (\x -> toText (fromString "\t" <> fromText x)) . T.lines . toText

instance Cps.HasThunk AsText where
  thunk t f = D $ do
    binder <- freshLabel
    let C body = f (S $ pure binder)
    body' <- body
    pure $ fromString "thunk " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body'
  force (D f) (S x) = C $ do
    f' <- f
    x' <- x
    pure $ fromString "! " <> f' <> fromString " " <> x'

instance Cps.HasReturn AsText where
  letTo t f = S $ do
    binder <- fresh
    let C body = f (D $ pure binder)
    body' <- body
    pure $ fromString "to " <> binder <> fromString ": " <> showb t <> fromString ".\n" <> body'

  returns (D x) (S k) = C $ do
    x' <- x
    k' <- k
    pure $ fromString "return " <> x' <> fromString " " <> k'

instance Cps.HasFn AsText where
  lambda (S k) f = C $ do
    binder <- fresh
    lbl <- freshLabel
    let C body = f (D $ pure binder) (S $ pure lbl)
    k' <- k
    body' <- body
    pure $ k' <> fromString " λ " <> binder <> fromString " " <> lbl <> fromString " →\n" <> body'
  D x <*> S k = S $ do
    x' <- x
    k' <- k
    pure $ x' <> fromString " :: " <> k'

instance Cps.HasCall AsText where
  call g = D $ pure $ fromString "call " <> showb g
