{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module View (View (..)) where

import Basic
import qualified Cbpv
import Common
import Const
import qualified Data.Text as T
import Explicit
import TextShow
import Tuple
import qualified Unique

data View

instance TextShow (AlgRep View a) where
  showb (V x) = Unique.withStream x

instance TextShow (SetRep View a) where
  showb (VS x) = Unique.withStream x

instance Basic View where
  newtype AlgRep View a = V (forall s. Unique.Stream s -> Builder)
  global g = V $ \_ -> showb g

instance Const View where
  newtype SetRep View a = VS (forall s. Unique.Stream s -> Builder)
  constant k = VS $ \_ -> showb k
  unit = VS $ \_ -> fromString "."

instance Tuple View

instance Explicit View where
  returns (VS value) = V $ \s -> fromString "return " <> value s

  letTo (V x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (VS $ \_ -> binder)
     in x xs <> fromString " to " <> binder <> fromString ".\n" <> y ys
  letBe (VS x) f = V $ \(Unique.Stream newId xs ys) ->
    let binder = fromString "v" <> showb newId
        V y = f (VS $ \_ -> binder)
     in x xs <> fromString " be " <> binder <> fromString ".\n" <> y ys

  lambda t f = V $ \(Unique.Stream newId _ s) ->
    let binder = fromString "v" <> showb newId
        V body = f (VS $ \_ -> binder)
     in fromString "λ " <> binder <> fromString ": " <> showb t <> fromString " →\n" <> body s
  apply (V f) (VS x) = V $ \(Unique.Stream _ fs xs) -> x xs <> fromString "\n" <> f fs

instance Cbpv.Cbpv View where
  thunk (V code) = VS $ \s -> fromString "thunk {" <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> code s))) <> fromString "\n}"
  force (VS thunk) = V $ \s -> fromString "! " <> thunk s
