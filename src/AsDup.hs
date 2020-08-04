{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsDup (AsDup, Code, Data, Stack, extract, extractData, extractStack) where

import Cbpv
import Common
import Control.Category
import qualified Cps
import qualified Cps
import Global
import HasCall
import HasConstants
import HasLet
import HasTuple
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import NatTrans
import PairF
import qualified Path
import SystemF (SystemF)
import qualified SystemF as F
import qualified Unique
import Prelude hiding ((.), (<*>))

extract :: Code cd dta k cd' dta' k' :~> PairF cd cd'
extract = NatTrans $ \(C x y) -> PairF x y

extractData :: Data cd dta k cd' dta' k' :~> PairF dta dta'
extractData = NatTrans $ \(D x y) -> PairF x y

extractStack :: Stack cd dta k cd' dta' k' :~> PairF k k'
extractStack = NatTrans $ \(S x y) -> PairF x y

data AsDup s t

data
  Code
    (cd :: Algebra -> *)
    (dta :: Set -> *)
    (k :: Algebra -> *)
    (cd' :: Algebra -> *)
    (dta' :: Set -> *)
    (k' :: Algebra -> *)
    a
  = C (cd a) (cd' a)

data
  Data
    (cd :: Algebra -> *)
    (dta :: Set -> *)
    (k :: Algebra -> *)
    (cd' :: Algebra -> *)
    (dta' :: Set -> *)
    (k' :: Algebra -> *)
    a
  = D (dta a) (dta' a)

data
  Stack
    (cd :: Algebra -> *)
    (dta :: Set -> *)
    (k :: Algebra -> *)
    (cd' :: Algebra -> *)
    (dta' :: Set -> *)
    (k' :: Algebra -> *)
    a
  = S (k a) (k' a)

instance (HasCall cd, HasCall cd') => HasCall (Code cd dta k cd' dta' k') where
  call g = C (call g) (call g)

instance (Cps.HasCall dta, Cps.HasCall dta') => Cps.HasCall (Data cd dta k cd' dta' k') where
  call g = D (Cps.call g) (Cps.call g)

instance (F.HasConstants cd, F.HasConstants cd') => F.HasConstants (Code cd dta k cd' dta' k') where
  constant k = C (F.constant k) (F.constant k)

instance (HasConstants dta, HasConstants dta') => HasConstants (Data cd dta k cd' dta' k') where
  constant k = D (constant k) (constant k)

instance (F.HasLet cd, F.HasLet cd') => F.HasLet (Code cd dta k cd' dta' k') where
  whereIs f (C l r) = C first second
    where
      first = F.letBe l $ \x' -> case f (C x' undefined) of
        C y _ -> y
      second = F.letBe r $ \x' -> case f (C undefined x') of
        C _ y -> y

instance (HasLet cd dta, HasLet cd' dta') => HasLet (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') where
  whereIs f (D l r) = C first second
    where
      first = letBe l $ \x' -> case f (D x' undefined) of
        C y _ -> y
      second = letBe r $ \x' -> case f (D undefined x') of
        C _ y -> y

instance (Cps.HasLabel cd k, Cps.HasLabel cd' k') => Cps.HasLabel (Code cd dta k cd' dta' k') (Stack cd dta k cd' dta' k') where
  label (S l r) f = C first second
    where
      first = Cps.label l $ \x' -> case f (S x' undefined) of
        C y _ -> y
      second = Cps.label r $ \x' -> case f (S undefined x') of
        C _ y -> y

instance (HasThunk cd dta, HasThunk cd' dta') => HasThunk (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') where
  thunk (C x y) = D (thunk x) (thunk y)
  force (D x y) = C (force x) (force y)

instance (HasReturn cd dta, HasReturn cd' dta') => HasReturn (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') where
  returns (D x y) = C (returns x) (returns y)
  from f (C l r) = C first second
    where
      first = letTo l $ \x' -> case f (D x' undefined) of
        C y _ -> y
      second = letTo r $ \x' -> case f (D undefined x') of
        C _ y -> y

instance (F.HasTuple cd, F.HasTuple cd) => F.HasTuple (Code cd dta k cd' dta' k')

instance (HasTuple cd dta, HasTuple cd' dta') => HasTuple (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k')

instance (Cps.HasReturn cd dta k, Cps.HasReturn cd' dta' k') => Cps.HasReturn (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') (Stack cd dta k cd' dta' k') where
  returns (D x x') (S k k') = C (Cps.returns x k) (Cps.returns x' k')
  letTo t f = S first second
    where
      first = Cps.letTo t $ \x -> case f (D x undefined) of
        C y _ -> y
      second = Cps.letTo t $ \x -> case f (D undefined x) of
        C _ y -> y

instance (Cps.HasThunk cd dta k, Cps.HasThunk cd' dta' k') => Cps.HasThunk (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') (Stack cd dta k cd' dta' k') where
  force (D x x') (S k k') = C (Cps.force x k) (Cps.force x' k')
  thunk t f = D first second
    where
      first = Cps.thunk t $ \x -> case f (S x undefined) of
        C y _ -> y
      second = Cps.thunk t $ \x -> case f (S undefined x) of
        C _ y -> y

instance (F.HasFn cd, F.HasFn cd') => F.HasFn (Code cd dta k cd' dta' k') where
  lambda t f = C first second
    where
      first = F.lambda t (Path.make getfirst . f . Path.make (\x -> C x undefined))
      second = F.lambda t (Path.make getsnd . f . Path.make (\x -> C undefined x))
      getfirst (C y _) = y
      getsnd (C _ y) = y

  C f f' <*> C x x' = C (f F.<*> x) (f' F.<*> x')

instance (Cps.HasFn cd dta k, Cps.HasFn cd' dta' k') => Cps.HasFn (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') (Stack cd dta k cd' dta' k') where
  lambda (S k k') f = C first second
    where
      first = Cps.lambda k $ \x n -> case f (D x undefined) (S n undefined) of
        C y _ -> y
      second = Cps.lambda k' $ \x n -> case f (D undefined x) (S undefined n) of
        C _ y -> y

  D f f' <*> S x x' = S (f Cps.<*> x) (f' Cps.<*> x')

instance (HasFn cd dta, HasFn cd' dta') => HasFn (Code cd dta k cd' dta' k') (Data cd dta k cd' dta' k') where
  lambda t f = C first second
    where
      first = lambda t $ \x -> case f (D x undefined) of
        C y _ -> y
      second = lambda t $ \x -> case f (D undefined x) of
        C _ y -> y

  C f f' <*> D x x' = C (f <*> x) (f' <*> x')
