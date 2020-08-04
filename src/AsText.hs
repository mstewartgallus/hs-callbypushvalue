{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module AsText (Code, Data, Stack, extract, extractData, AsText) where

import Cbpv
import Common
import qualified Cps
import qualified Data.Text as T
import HasCall
import HasConstants
import HasLet
import HasTuple
import qualified Path
import qualified SystemF
import TextShow
import qualified Unique

data AsText

extract :: Code a -> T.Text
extract (C x) = toText (Unique.withStream x)

extractData :: Data a -> T.Text
extractData (D x) = toText (Unique.withStream x)

newtype Data (a :: Set) = D (forall s. Unique.Stream s -> Builder)

newtype Code (a :: Algebra) = C {unC :: forall s. Unique.Stream s -> Builder}

newtype Stack (a :: Algebra) = S (forall s. Unique.Stream s -> TextShow.Builder)

instance HasCall Code where
  call g = C $ \_ -> fromString "call " <> showb g

instance SystemF.HasConstants Code where
  constant k = C $ \_ -> showb k

instance HasConstants Data where
  constant k = D $ \_ -> showb k

instance HasTuple Code Data where
  pair (D x) (D y) = D $ \(Unique.Stream _ xs ys) ->
    let x' = x xs
        y' = y ys
     in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"

  unpair (D tuple) f = C $ \(Unique.Stream xId ts (Unique.Stream yId _ bodys)) ->
    let x = fromString "v" <> showb xId
        y = fromString "v" <> showb yId
        C body = f (D $ \_ -> x) (D $ \_ -> y)
     in tuple ts <> fromString " unpair (" <> x <> fromString ", " <> y <> fromString ")\n" <> body bodys

instance HasReturn Code Data where
  letTo (C x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        C y = f (D $ \_ -> binder)
     in x xs <> fromString " to " <> binder <> fromString ".\n" <> y ys
  returns (D k) = C $ \s ->
    fromString "return " <> k s

instance SystemF.HasTuple Code where
  pair (C x) (C y) = C $ \(Unique.Stream _ xs ys) ->
    let x' = x xs
        y' = y ys
     in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"

  unpair (C tuple) f = C $ \(Unique.Stream xId ts (Unique.Stream yId _ bodys)) ->
    let x = fromString "l" <> showb xId
        y = fromString "l" <> showb yId
        C body = f (C $ \_ -> x) (C $ \_ -> y)
     in tuple ts <> fromString " unpair (" <> x <> fromString ", " <> y <> fromString ")\n" <> body bodys

instance SystemF.HasLet Code where
  letBe (C x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "l" <> showb newId
        C y = f (C $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

instance SystemF.HasFn Code where
  lambda t f = C $ \(Unique.Stream newId _ ys) ->
    let binder = fromString "v" <> showb newId
        C y = Path.flatten f (C $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> y ys
  C f <*> C x = C $ \(Unique.Stream _ fs xs) ->
    fromString "(" <> f fs <> fromString " " <> x xs <> fromString ")"

instance HasLet Code Data where
  letBe (D x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        C y = f (D $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

instance Cps.HasLabel Code Stack where
  label (S x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "l" <> showb newId
        C y = f (S $ \_ -> binder)
     in x xs <> fromString " label " <> binder <> fromString ".\n" <> y ys

instance HasFn Code Data where
  C f <*> D x = C $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n" <> f fs
  lambda t f = C $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        C body = f (D $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s

instance HasThunk Code Data where
  thunk (C code) = D $ \s -> fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> code s))) <> fromString "\n}"
  force (D th) = C $ \s -> fromString "! " <> th s

instance Cps.HasThunk Code Data Stack where
  thunk t f = D $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        C body = f (S $ \_ -> binder)
     in fromString "thunk " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  force (D f) (S x) = C $ \(Unique.Stream _ fs xs) -> fromString "! " <> f fs <> fromString " " <> x xs

instance Cps.HasReturn Code Data Stack where
  letTo t f = S $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        C body = f (D $ \_ -> binder)
     in fromString "to " <> binder <> fromString ": " <> showb t <> fromString ".\n" <> body s

  returns (D x) (S k) = C $ \(Unique.Stream _ ks xs) ->
    fromString "return " <> x xs <> fromString " " <> k ks

instance Cps.HasFn Code Data Stack where
  lambda (S k) f = C $ \(Unique.Stream h ks (Unique.Stream t _ s)) ->
    let binder = fromString "v" <> showb h
        lbl = fromString "l" <> showb t
        C body = f (D $ \_ -> binder) (S $ \_ -> lbl)
     in k ks <> fromString " λ " <> binder <> fromString " " <> lbl <> fromString " →\n" <> body s
  D x <*> S k = S $ \(Unique.Stream _ ks xs) ->
    x xs <> fromString " :: " <> k ks

instance Cps.HasCall Data where
  call g = D $ \_ -> fromString "call " <> showb g
