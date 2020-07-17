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
import Explicit
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetLabel
import qualified HasStack
import qualified HasThunk
import qualified Pure
import qualified SystemF
import TextShow
import Tuple
import qualified Unique

data AsText

extract :: CodeRep AsText a -> T.Text
extract (V x) = toText (Unique.withStream x)

extractData :: DataRep AsText a -> T.Text
extractData (VS x) = toText (Unique.withStream x)

instance HasData AsText where
  newtype DataRep AsText a = VS (forall s. Unique.Stream s -> Builder)

instance HasCode AsText where
  newtype CodeRep AsText a = V (forall s. Unique.Stream s -> Builder)

instance HasGlobals AsText where
  global g = V $ \_ -> showb g

instance HasConstants AsText where
  constant k = VS $ \_ -> showb k
  unit = VS $ \_ -> fromString "."

instance Tuple AsText

instance Pure.Pure AsText where
  pure (VS k) = V $ \s ->
    fromString "(pure " <> k s <> fromString ")"

instance SystemF.SystemF AsText where
  pair (V x) (V y) = V $ \(Unique.Stream _ xs ys) ->
    let x' = x xs
        y' = y ys
     in fromString "(" <> x' <> fromString ", " <> y' <> fromString ")"

  letBe (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "l" <> showb newId
        V y = f (V $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = V $ \(Unique.Stream newId _ ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (V $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ".\n" <> y ys

  V f <*> V x = V $ \(Unique.Stream _ fs xs) ->
    fromString "(" <> f fs <> fromString " " <> x xs <> fromString ")"

instance HasLet AsText where
  letBe (VS x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (VS $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

instance Explicit AsText where
  letTo (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (VS $ \_ -> binder)
     in x xs <> fromString " to " <> binder <> fromString ".\n" <> y ys

  apply (V f) (VS x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n" <> f fs

instance Cbpv.Cbpv AsText where
  lambda t f = V $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        V body = f (VS $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  thunk (V code) = VS $ \s -> fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> code s))) <> fromString "\n}"
  force (VS thunk) = V $ \s -> fromString "! " <> thunk s

instance HasStack.HasStack AsText where
  data StackRep AsText a = VStk (forall s. Unique.Stream s -> TextShow.Builder)

instance HasThunk.HasThunk AsText where
  lambda (VStk k) f = V $ \(Unique.Stream h ks (Unique.Stream t _ s)) ->
    let binder = fromString "v" <> showb h
        lbl = fromString "l" <> showb t
        V body = f (VS $ \_ -> binder) (VStk $ \_ -> lbl)
     in k ks <> fromString " λ " <> binder <> fromString " " <> lbl <> fromString " →\n" <> body s
  thunk t f = VS $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        V body = f (VStk $ \_ -> binder)
     in fromString "thunk " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  force (VS f) (VStk x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n! " <> f fs

  call g (VStk k) = V $ \s -> fromString "call " <> showb g <> fromString " " <> k s

instance Callcc.Callcc AsText where
  catch t f = V $ \(Unique.Stream newId _ s) ->
    let binder = fromString "l" <> showb newId
        V body = f (VStk $ \_ -> binder)
     in fromString "catch " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  throw (VStk f) (V x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\nthrow " <> f fs

instance HasLetLabel AsText

instance Cps.Cps AsText where
  letTo t f = VStk $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        V body = f (VS $ \_ -> binder)
     in fromString "to " <> binder <> fromString ": " <> showb t <> fromString ".\n" <> body s

  throw (VStk k) (VS x) = V $ \(Unique.Stream _ ks xs) ->
    fromString "throw " <> k ks <> fromString " " <> x xs

  apply (VS x) (VStk k) = VStk $ \(Unique.Stream _ ks xs) ->
    k ks <> fromString "  :: " <> x xs
