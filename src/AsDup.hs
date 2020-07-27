{-# LANGUAGE TypeFamilies #-}

module AsDup (AsDup, extract, extractData) where

import Cbpv
import Common
import qualified Cps
import qualified Cps
import Global
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import SystemF (SystemF)
import qualified SystemF as F
import qualified Unique
import Prelude hiding ((<*>))

extract :: Code (AsDup s t) a -> (Code s a, Code t a)
extract (C x y) = (x, y)

extractData :: Data (AsDup s t) a -> (Data s a, Data t a)
extractData (D x y) = (x, y)

data AsDup s t

instance HasCode (AsDup s t) where
  data Code (AsDup s t) a = C (Code s a) (Code t a)

instance HasData (AsDup s t) where
  data Data (AsDup s t) a = D (Data s a) (Data t a)

instance HasStack (AsDup s t) where
  data Stack (AsDup s t) a = S (Stack s a) (Stack t a)

instance (HasCall s, HasCall t) => HasCall (AsDup s t) where
  call g = C (call g) (call g)

instance (Cps.HasCall s, Cps.HasCall t) => Cps.HasCall (AsDup s t) where
  call g = D (Cps.call g) (Cps.call g)

instance (F.HasConstants s, F.HasConstants t) => F.HasConstants (AsDup s t) where
  constant k = C (F.constant k) (F.constant k)

instance (HasConstants s, HasConstants t) => HasConstants (AsDup s t) where
  constant k = D (constant k) (constant k)

instance (F.HasLet s, F.HasLet t) => F.HasLet (AsDup s t) where
  letBe (C l r) f = C first second
    where
      first = F.letBe l $ \x' -> case f (C x' undefined) of
        C y _ -> y
      second = F.letBe r $ \x' -> case f (C undefined x') of
        C _ y -> y

instance (HasLet s, HasLet t) => HasLet (AsDup s t) where
  letBe (D l r) f = C first second
    where
      first = letBe l $ \x' -> case f (D x' undefined) of
        C y _ -> y
      second = letBe r $ \x' -> case f (D undefined x') of
        C _ y -> y

instance (Cps.HasLabel s, Cps.HasLabel t) => Cps.HasLabel (AsDup s t) where
  label (S l r) f = C first second
    where
      first = Cps.label l $ \x' -> case f (S x' undefined) of
        C y _ -> y
      second = Cps.label r $ \x' -> case f (S undefined x') of
        C _ y -> y

instance (HasThunk s, HasThunk t) => HasThunk (AsDup s t) where
  thunk (C x y) = D (thunk x) (thunk y)
  force (D x y) = C (force x) (force y)

instance (HasReturn s, HasReturn t) => HasReturn (AsDup s t) where
  returns (D x y) = C (returns x) (returns y)
  letTo (C l r) f = C first second
    where
      first = letTo l $ \x' -> case f (D x' undefined) of
        C y _ -> y
      second = letTo r $ \x' -> case f (D undefined x') of
        C _ y -> y

instance (F.HasTuple s, F.HasTuple t) => F.HasTuple (AsDup s t)

instance (HasTuple s, HasTuple t) => HasTuple (AsDup s t)

instance (Cps.HasReturn s, Cps.HasReturn t) => Cps.HasReturn (AsDup s t) where
  returns (D x x') (S k k') = C (Cps.returns x k) (Cps.returns x' k')
  letTo t f = S first second
    where
      first = Cps.letTo t $ \x -> case f (D x undefined) of
        C y _ -> y
      second = Cps.letTo t $ \x -> case f (D undefined x) of
        C _ y -> y

instance (Cps.HasThunk s, Cps.HasThunk t) => Cps.HasThunk (AsDup s t) where
  force (D x x') (S k k') = C (Cps.force x k) (Cps.force x' k')
  thunk t f = D first second
    where
      first = Cps.thunk t $ \x -> case f (S x undefined) of
        C y _ -> y
      second = Cps.thunk t $ \x -> case f (S undefined x) of
        C _ y -> y

instance (F.HasFn s, F.HasFn t) => F.HasFn (AsDup s t) where
  lambda t f = C first second
    where
      first = F.lambda t $ \x -> case f (C x undefined) of
        C y _ -> y
      second = F.lambda t $ \x -> case f (C undefined x) of
        C _ y -> y

  C f f' <*> C x x' = C (f F.<*> x) (f' F.<*> x')

instance (Cps.HasFn s, Cps.HasFn t) => Cps.HasFn (AsDup s t) where
  lambda (S k k') f = C first second
    where
      first = Cps.lambda k $ \x n -> case f (D x undefined) (S n undefined) of
        C y _ -> y
      second = Cps.lambda k' $ \x n -> case f (D undefined x) (S undefined n) of
        C _ y -> y

  D f f' <*> S x x' = S (f Cps.<*> x) (f' Cps.<*> x')

instance (HasFn s, HasFn t) => HasFn (AsDup s t) where
  lambda t f = C first second
    where
      first = lambda t $ \x -> case f (D x undefined) of
        C y _ -> y
      second = lambda t $ \x -> case f (D undefined x) of
        C _ y -> y

  C f f' <*> D x x' = C (f <*> x) (f' <*> x')
