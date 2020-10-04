{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module MonoInliner (extractTerm, extract, extractData, MonoInliner) where

import Cbpv
import Control.Category
import qualified Cps
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTerm
import HasTerminal
import HasTuple
import NatTrans
import qualified SystemF
import Prelude hiding ((.), (<*>))

data MonoInliner t

extractTerm :: Term (MonoInliner t) :~> Term t
extractTerm = NatTrans $ \(T _ x) -> x

extract :: Code (MonoInliner t) :~> Code t
extract = NatTrans $ \(C _ x) -> x

extractData :: Data (MonoInliner t) :~> Data t
extractData = NatTrans $ \(D _ x) -> x

instance HasTerm t => HasTerm (MonoInliner t) where
  data Term (MonoInliner t) a = T Int (Term t a)

instance HasCode t => HasCode (MonoInliner t) where
  data Code (MonoInliner t) a = C Int (Code t a)

instance HasData t => HasData (MonoInliner t) where
  data Data (MonoInliner t) a = D Int (Data t a)

instance HasStack t => HasStack (MonoInliner t) where
  data Stack (MonoInliner t) a = S Int (Stack t a)

instance HasCall t => HasCall (MonoInliner t) where
  call g = C 0 (call g)

instance HasTerminal t => HasTerminal (MonoInliner t) where
  terminal = D 0 terminal

instance HasConstants t => HasConstants (MonoInliner t) where
  constant k = D 0 (constant k)

instance SystemF.HasConstants t => SystemF.HasConstants (MonoInliner t) where
  constant k = T 0 (SystemF.constant k)

instance HasTuple t => HasTuple (MonoInliner t)

instance HasLet t => HasLet (MonoInliner t) where
  whereIs f (D xcost x) = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (D 1 x)
      notinlined = C (xcost + fcost) $
        letBe x $ \x' -> case f (D 0 x') of
          C _ y -> y
      C fcost _ = f (D 0 x)

instance Cps.HasLabel t => Cps.HasLabel (MonoInliner t) where
  label (S xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (S 1 x)
      notinlined = C (xcost + fcost) $
        Cps.label x $ \x' -> case f (S 0 x') of
          C _ y -> y
      C fcost _ = f (S 0 x)

instance HasReturn t => HasReturn (MonoInliner t) where
  returns (D cost k) = C cost (returns k)
  from f (C xcost x) =
    let C fcost _ = f (D 0 undefined)
     in C (xcost + fcost) $
          letTo x $ \x' -> case f (D 0 x') of
            C _ y -> y

instance HasFn t => HasFn (MonoInliner t) where
  C fcost f <*> D xcost x = C (fcost + xcost) (f <*> x)
  lambda t f =
    let C fcost _ = f (D 0 undefined)
     in C fcost $
          lambda t $ \x' -> case f (D 0 x') of
            C _ y -> y

instance HasThunk t => HasThunk (MonoInliner t) where
  force (D cost th) = C cost (force th)
  thunk (C cost code) = D cost (thunk code)

instance Cps.HasThunk t => Cps.HasThunk (MonoInliner t) where
  thunk t f =
    let C fcost _ = f (S 0 undefined)
     in D fcost $
          Cps.thunk t $ \x' -> case f (S 0 x') of
            C _ y -> y
  force (D tcost th) (S scost stack) = C (tcost + scost) (Cps.force th stack)

instance Cps.HasReturn t => Cps.HasReturn (MonoInliner t) where
  letTo t f =
    let C fcost _ = f (D 0 undefined)
     in S fcost $
          Cps.letTo t $ \x' -> case f (D 0 x') of
            C _ y -> y
  returns (D scost c) (S tcost stk) = C (tcost + scost) (Cps.returns c stk)

instance Cps.HasFn t => Cps.HasFn (MonoInliner t) where
  D xcost x <*> S kcost k = S (xcost + kcost) (x Cps.<*> k)
  lambda (S kcost k) f =
    let C fcost _ = f (D 0 undefined) (S 0 undefined)
     in C (kcost + fcost) $
          Cps.lambda k $ \x n -> case f (D 0 x) (S 0 n) of
            C _ y -> y

instance Cps.HasCall t => Cps.HasCall (MonoInliner t) where
  call = D 0 . Cps.call

instance SystemF.HasTuple t => SystemF.HasTuple (MonoInliner t) where
  pair f g (T xcost x) =
    let T fcost _ = f (T 0 undefined)
        T gcost _ = g (T 0 undefined)
     in T (fcost + gcost + xcost) $ SystemF.pair ((extractTerm #) . f . T 0) ((extractTerm #) . g . T 0) x
  first (T tcost tuple) = T tcost $ SystemF.first tuple
  second (T tcost tuple) = T tcost $ SystemF.second tuple

instance SystemF.HasLet t => SystemF.HasLet (MonoInliner t) where
  whereIs f (T xcost x) = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(T inlineCost _) = f (T 1 x)
      notinlined = T (xcost + fcost) $
        SystemF.letBe x $ \x' -> case f (T 0 x') of
          T _ y -> y
      T fcost _ = f (T 0 x)

instance SystemF.HasFn t => SystemF.HasFn (MonoInliner t) where
  lambda t f =
    let T fcost _ = f (T 0 undefined)
     in T fcost $ SystemF.lambda t ((extractTerm #) . f . (T 0))
  T fcost f <*> T xcost x = T (fcost + xcost) (f SystemF.<*> x)

instance SystemF.HasCall t => SystemF.HasCall (MonoInliner t) where
  call g = T 0 (SystemF.call g)
