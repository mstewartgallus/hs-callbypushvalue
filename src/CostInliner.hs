{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CostInliner (extract, extractData, CostInliner) where

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
import qualified SystemF
import Prelude hiding ((.), (<*>))

data CostInliner t

extract :: Code (CostInliner t) :~> Code t
extract = NatTrans $ \(C _ x) -> x

extractData :: Data (CostInliner t) :~> Data t
extractData = NatTrans $ \(D _ x) -> x

maxInline :: Int
maxInline = 5

instance HasCode t => HasCode (CostInliner t) where
  data Code (CostInliner t) a = C Int (Code t a)

instance HasData t => HasData (CostInliner t) where
  data Data (CostInliner t) a = D Int (Data t a)

instance HasStack t => HasStack (CostInliner t) where
  data Stack (CostInliner t) a = S Int (Stack t a)

instance HasCall t => HasCall (CostInliner t) where
  call g = C 0 (call g)

instance HasTerminal t => HasTerminal (CostInliner t) where
  terminal = D 0 terminal

instance HasConstants t => HasConstants (CostInliner t) where
  constant k = D 0 (constant k)

instance SystemF.HasConstants t => SystemF.HasConstants (CostInliner t) where
  constant k = C 0 (SystemF.constant k)

instance HasTuple t => HasTuple (CostInliner t)

instance SystemF.HasLet t => SystemF.HasLet (CostInliner t) where
  whereIs f (C xcost x) = result
    where
      result
        | inlineCost <= maxInline = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (C 1 x)
      notinlined = C (1 + xcost + fcost) $
        SystemF.letBe x $ \x' -> case f (C 0 x') of
          C _ y -> y
      C fcost _ = f (C 0 x)

instance HasLet t => HasLet (CostInliner t) where
  whereIs f (D xcost x) = result
    where
      result
        | inlineCost <= maxInline = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (D 0 x)
      notinlined = C (xcost + fcost) $
        letBe x $ \x' -> case f (D 0 x') of
          C _ y -> y
      C fcost _ = f (D 0 x)

instance Cps.HasLabel t => Cps.HasLabel (CostInliner t) where
  label (S xcost x) f = result
    where
      result
        | inlineCost <= maxInline = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (S 0 x)
      notinlined = C (xcost + fcost) $
        Cps.label x $ \x' -> case f (S 0 x') of
          C _ y -> y
      C fcost _ = f (S 0 x)

instance HasReturn t => HasReturn (CostInliner t) where
  from f (C xcost x) =
    let C fcost _ = f (D 0 undefined)
     in C (1 + xcost + fcost) $
          letTo x $ \x' -> case f (D 0 x') of
            C _ y -> y
  returns (D cost k) = C (1 + cost) (returns k)

instance HasFn t => HasFn (CostInliner t) where
  C fcost f <*> D xcost x = C (1 + fcost + xcost) (f <*> x)
  lambda t f =
    let C fcost _ = f (D 0 undefined)
     in C (1 + fcost) $
          lambda t $ \x' -> case f (D 0 x') of
            C _ y -> y

instance HasThunk t => HasThunk (CostInliner t) where
  force (D cost th) = C (1 + cost) (force th)
  thunk (C cost code) = D (1 + cost) (thunk code)

instance Cps.HasThunk t => Cps.HasThunk (CostInliner t) where
  thunk t f =
    let C fcost _ = f (S 0 undefined)
     in D (1 + fcost) $
          Cps.thunk t $ \x' -> case f (S 0 x') of
            C _ y -> y
  force (D tcost th) (S scost stack) = C (1 + tcost + scost) (Cps.force th stack)

instance Cps.HasReturn t => Cps.HasReturn (CostInliner t) where
  letTo t f =
    let C fcost _ = f (D 0 undefined)
     in S (1 + fcost) $
          Cps.letTo t $ \x' -> case f (D 0 x') of
            C _ y -> y
  returns (D scost c) (S tcost stk) = C (1 + tcost + scost) (Cps.returns c stk)

instance Cps.HasFn t => Cps.HasFn (CostInliner t) where
  D xcost x <*> S kcost k = S (1 + xcost + kcost) (x Cps.<*> k)
  lambda (S kcost k) f =
    let C fcost _ = f (D 0 undefined) (S 0 undefined)
     in C (1 + kcost + fcost) $
          Cps.lambda k $ \x n -> case f (D 0 x) (S 0 n) of
            C _ y -> y

instance Cps.HasCall t => Cps.HasCall (CostInliner t) where
  call = D 0 . Cps.call

instance SystemF.HasTuple t => SystemF.HasTuple (CostInliner t) where
  pair f g (C xcost x) =
    let C fcost _ = f (C 0 undefined)
        C gcost _ = g (C 0 undefined)
     in C (1 + fcost + gcost + xcost) $ SystemF.pair ((extract #) . f . C 0) ((extract #) . g . C 0) x
  first (C tcost tuple) = C (1 + tcost) $ SystemF.first tuple
  second (C tcost tuple) = C (1 + tcost) $ SystemF.second tuple

instance SystemF.HasFn t => SystemF.HasFn (CostInliner t) where
  lambda t f =
    let C fcost _ = f (C 0 undefined)
     in C (1 + fcost) $ SystemF.lambda t ((extract #) . f . (C 0))
  C fcost f <*> C xcost x = C (1 + fcost + xcost) (f SystemF.<*> x)
