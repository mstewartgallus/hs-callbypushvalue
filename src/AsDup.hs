{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsDup (AsDup, extract, extractData, extractStack) where

import Cbpv
import Control.Category
import qualified Cps
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTerminal
import HasTuple
import NatTrans
import PairF
import qualified SystemF as F
import Prelude hiding ((.), (<*>))

extract :: Code (AsDup s t) :~> PairF (Code s) (Code t)
extract = NatTrans $ \(C x y) -> PairF x y

extractData :: Data (AsDup s t) :~> PairF (Data s) (Data t)
extractData = NatTrans $ \(D x y) -> PairF x y

extractStack :: Stack (AsDup s t) :~> PairF (Stack s) (Stack t)
extractStack = NatTrans $ \(S x y) -> PairF x y

factorizeC :: (c -> Code s a) -> (c -> Code t a) -> c -> Code (AsDup s t) a
factorizeC f g x = C (f x) (g x)

factorizeD :: (c -> Data s a) -> (c -> Data t a) -> c -> Data (AsDup s t) a
factorizeD f g x = D (f x) (g x)

data AsDup s t

instance HasCode (AsDup s t) where
  data Code (AsDup s t) a = C {fstC :: Code s a, sndC :: Code t a}

instance HasData (AsDup s t) where
  data Data (AsDup s t) a = D {fstD :: Data s a, sndD :: Data t a}

instance HasStack (AsDup s t) where
  data Stack (AsDup s t) a = S {fstS :: Stack s a, sndS :: Stack t a}

instance (HasTerminal s, HasTerminal t) => HasTerminal (AsDup s t) where
  terminal = D terminal terminal

instance (HasCall s, HasCall t) => HasCall (AsDup s t) where
  call = factorizeC call call

instance (Cps.HasCall s, Cps.HasCall t) => Cps.HasCall (AsDup s t) where
  call = factorizeD Cps.call Cps.call

instance (F.HasConstants s, F.HasConstants t) => F.HasConstants (AsDup s t) where
  constant = factorizeC F.constant F.constant

instance (HasConstants s, HasConstants t) => HasConstants (AsDup s t) where
  constant = factorizeD constant constant

instance (F.HasLet s, F.HasLet t) => F.HasLet (AsDup s t) where
  whereIs f = factorizeC first second
    where
      first (C l r) = F.whereIs (\x' -> fstC $ f (C x' r)) l
      second (C l r) = F.whereIs (\x' -> sndC $ f (C l x')) r

instance (HasLet s, HasLet t) => HasLet (AsDup s t) where
  whereIs f = factorizeC first second
    where
      first (D l r) = whereIs (\x' -> fstC $ f (D x' r)) l
      second (D l r) = whereIs (\x' -> sndC $ f (D l x')) r

instance (Cps.HasLabel s, Cps.HasLabel t) => Cps.HasLabel (AsDup s t) where
  whereLabel f = factorizeC first second
    where
      first (S l r) = Cps.whereLabel (\x' -> fstC $ f (S x' r)) l
      second (S l r) = Cps.whereLabel (\x' -> sndC $ f (S l x')) r

instance (HasThunk s, HasThunk t) => HasThunk (AsDup s t) where
  thunk = factorizeD (thunk . fstC) (thunk . sndC)
  force = factorizeC (force . fstD) (force . sndD)

instance (HasReturn s, HasReturn t) => HasReturn (AsDup s t) where
  returns = factorizeC (returns . fstD) (returns . sndD)
  from f = factorizeC first second
    where
      first = from (\x' -> fstC $ f (D x' undefined)) . fstC
      second = from (\x' -> sndC $ f (D undefined x')) . sndC

instance (F.HasTuple s, F.HasTuple t) => F.HasTuple (AsDup s t) where
  pair f g = factorizeC first second
    where
      first (C l r) =
        F.pair
          (\x -> fstC $ f (C x r))
          (\x -> fstC $ g (C x r))
          l
      second (C l r) =
        F.pair
          (\x -> sndC $ f (C l x))
          (\x -> sndC $ g (C l x))
          r
  first = factorizeC (F.first . fstC) (F.first . sndC)
  second = factorizeC (F.second . fstC) (F.second . sndC)

instance (HasTuple s, HasTuple t) => HasTuple (AsDup s t) where
  pair f g = factorizeD first second
    where
      first (D l r) =
        pair
          (\x -> fstD $ f (D x r))
          (\x -> fstD $ g (D x r))
          l
      second (D l r) =
        pair
          (\x -> sndD $ f (D l x))
          (\x -> sndD $ g (D l x))
          r
  first = factorizeD (first . fstD) (first . sndD)
  second = factorizeD (second . fstD) (second . sndD)

instance (Cps.HasReturn s, Cps.HasReturn t) => Cps.HasReturn (AsDup s t) where
  returns (D x x') (S k k') = C (Cps.returns x k) (Cps.returns x' k')
  letTo t f = S first second
    where
      first = Cps.letTo t $ \x -> fstC $ f (D x (probeData t))
      second = Cps.letTo t $ \x -> sndC $ f (D (probeData t) x)

instance (Cps.HasThunk s, Cps.HasThunk t) => Cps.HasThunk (AsDup s t) where
  force (D x x') (S k k') = C (Cps.force x k) (Cps.force x' k')
  thunk t f = D first second
    where
      first = Cps.thunk t $ \x -> fstC $ f (S x (probeStack t))
      second = Cps.thunk t $ \x -> sndC $ f (S (probeStack t) x)

instance (F.HasFn s, F.HasFn t) => F.HasFn (AsDup s t) where
  lambda t f = C first second
    where
      first = F.lambda t (fstC . f . (\x -> C x (probeCode t)))
      second = F.lambda t (sndC . f . (\x -> C (probeCode t) x))

  C f f' <*> C x x' = C (f F.<*> x) (f' F.<*> x')

instance (Cps.HasFn s, Cps.HasFn t) => Cps.HasFn (AsDup s t) where
  lambda (S k k') f = C first second
    where
      first = Cps.lambda k $ \x n -> fstC $ f (D x undefined) (S n undefined)
      second = Cps.lambda k' $ \x n -> sndC $ f (D undefined x) (S undefined n)

  D f f' <*> S x x' = S (f Cps.<*> x) (f' Cps.<*> x')

instance (HasFn s, HasFn t) => HasFn (AsDup s t) where
  lambda t f = C first second
    where
      first = lambda t (\x -> fstC $ f (D x (probeData t)))
      second = lambda t (\x -> sndC $ f (D (probeData t) x))

  C f f' <*> D x x' = C (f <*> x) (f' <*> x')
