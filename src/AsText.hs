{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module AsText (extract, extractData, AsText (..)) where

import qualified Callcc
import qualified Cbpv
import Common
import qualified Cps
import qualified Data.Text as T
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetLabel
import HasLetTo
import HasReturn
import qualified HasStack
import qualified HasThunk
import HasTuple
import qualified SystemF
import TextShow
import qualified Unique

data AsText

extract :: Code AsText a -> T.Text
extract (C x) = toText (Unique.withStream x)

extractData :: Data AsText a -> T.Text
extractData (D x) = toText (Unique.withStream x)

instance HasData AsText where
  newtype Data AsText a = D (forall s. Unique.Stream s -> Builder)

instance HasCode AsText where
  newtype Code AsText a = C (forall s. Unique.Stream s -> Builder)

instance HasGlobals AsText where
  global g = C $ \_ -> showb g

instance HasConstants AsText where
  constant k = D $ \_ -> showb k
  unit = D $ \_ -> fromString "."

instance HasTuple AsText

instance HasReturn AsText where
  returns (D k) = C $ \s ->
    fromString "(return " <> k s <> fromString ")"

instance SystemF.SystemF AsText where
  pair (C x) (C y) = C $ \(Unique.Stream _ xs ys) ->
    let x' = x xs
        y' = y ys
     in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"

  letBe (C x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "l" <> showb newId
        C y = f (C $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = C $ \(Unique.Stream newId _ ys) ->
    let binder = fromString "v" <> showb newId
        C y = f (C $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ".\n" <> y ys

  C f <*> C x = C $ \(Unique.Stream _ fs xs) ->
    fromString "(" <> f fs <> fromString " " <> x xs <> fromString ")"

instance HasLet AsText where
  letBe (D x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        C y = f (D $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

instance HasLetLabel AsText where
  letLabel (S x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "l" <> showb newId
        C y = f (S $ \_ -> binder)
     in x xs <> fromString " label " <> binder <> fromString ".\n" <> y ys

instance HasLetTo AsText where
  letTo (C x) f = C $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        C y = f (D $ \_ -> binder)
     in x xs <> fromString " to " <> binder <> fromString ".\n" <> y ys

  apply (C f) (D x) = C $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n" <> f fs

instance Cbpv.Cbpv AsText where
  lambda t f = C $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        C body = f (D $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  thunk (C code) = D $ \s -> fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> code s))) <> fromString "\n}"
  force (D thunk) = C $ \s -> fromString "! " <> thunk s

instance HasStack.HasStack AsText where
  data Stack AsText a = S (forall s. Unique.Stream s -> TextShow.Builder)

instance HasThunk.HasThunk AsText where
  lambda (S k) f = C $ \(Unique.Stream h ks (Unique.Stream t _ s)) ->
    let binder = fromString "v" <> showb h
        lbl = fromString "l" <> showb t
        C body = f (D $ \_ -> binder) (S $ \_ -> lbl)
     in k ks <> fromString " λ " <> binder <> fromString " " <> lbl <> fromString " →\n" <> body s
  thunk t f = D $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        C body = f (S $ \_ -> binder)
     in fromString "thunk " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  force (D f) (S x) = C $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n! " <> f fs

  call g (S k) = C $ \s -> fromString "call " <> showb g <> fromString " " <> k s

instance Callcc.Callcc AsText where
  catch t f = C $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        C body = f (S $ \_ -> binder)
     in fromString "catch " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  throw (S f) (C x) = C $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\nthrow " <> f fs

instance Cps.Cps AsText where
  letTo t f = S $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        C body = f (D $ \_ -> binder)
     in fromString "to " <> binder <> fromString ": " <> showb t <> fromString ".\n" <> body s

  throw (S k) (D x) = C $ \(Unique.Stream _ ks xs) ->
    fromString "throw " <> k ks <> fromString " " <> x xs

  apply (D x) (S k) = S $ \(Unique.Stream _ ks xs) ->
    k ks <> fromString " :: " <> x xs
