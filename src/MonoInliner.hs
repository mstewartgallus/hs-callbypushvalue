{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module MonoInliner (extract, extractData, MonoInliner) where

import qualified Callcc
import Cbpv
import Common
import qualified Cps
import qualified Data.Text as T
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetLabel
import HasLetTo
import HasReturn
import HasStack
import qualified HasThunk
import HasTuple
import Name
import qualified SystemF
import Prelude hiding ((<*>))

data MonoInliner t

extract :: Code (MonoInliner t) a -> Code t a
extract (C _ x) = x

extractData :: Data (MonoInliner t) a -> Data t a
extractData (D _ x) = x

instance HasCode t => HasCode (MonoInliner t) where
  data Code (MonoInliner t) a = C Int (Code t a)

instance HasData t => HasData (MonoInliner t) where
  data Data (MonoInliner t) a = D Int (Data t a)

instance HasStack t => HasStack (MonoInliner t) where
  data Stack (MonoInliner t) a = S Int (Stack t a)

instance HasGlobals t => HasGlobals (MonoInliner t) where
  global g = C 0 (global g)

instance HasConstants t => HasConstants (MonoInliner t) where
  constant k = D 0 (constant k)
  unit = D 0 unit

instance HasTuple t => HasTuple (MonoInliner t) where
  pair (D xcost x) (D ycost y) = D (xcost + ycost) (pair x y)
  unpair (D tcost tuple) f =
    let C rcost _ = f (D 0 undefined) (D 0 undefined)
     in C (tcost + rcost) $ unpair tuple $ \x y -> case f (D 0 x) (D 0 y) of
          C _ r -> r

instance HasLet t => HasLet (MonoInliner t) where
  letBe (D xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (D 1 x)
      notinlined = C (xcost + fcost) $ letBe x $ \x' -> case f (D 0 x') of
        C _ y -> y
      C fcost _ = f (D 0 x)

instance HasLetLabel t => HasLetLabel (MonoInliner t) where
  letLabel (S xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (S 1 x)
      notinlined = C (xcost + fcost) $ letLabel x $ \x' -> case f (S 0 x') of
        C _ y -> y
      C fcost _ = f (S 0 x)

instance HasLetTo t => HasLetTo (MonoInliner t) where
  letTo (C xcost x) f =
    let -- fixme... figure out a better probe...
        C fcost _ = f (D 0 undefined)
     in C (xcost + fcost) $ letTo x $ \x' -> case f (D 0 x') of
          C _ y -> y

  apply (C fcost f) (D xcost x) = C (fcost + xcost) (apply f x)

instance Cbpv t => Cbpv (MonoInliner t) where
  lambda t f =
    let C fcost _ = f (D 0 undefined)
     in C fcost $ lambda t $ \x' -> case f (D 0 x') of
          C _ y -> y
  force (D cost th) = C cost (force th)
  thunk (C cost code) = D cost (thunk code)

instance HasThunk.HasThunk t => HasThunk.HasThunk (MonoInliner t) where
  lambda (S kcost k) f =
    let C fcost _ = f (D 0 undefined) (S 0 undefined)
     in C (kcost + fcost) $ HasThunk.lambda k $ \x n -> case f (D 0 x) (S 0 n) of
          C _ y -> y
  thunk t f =
    let C fcost _ = f (S 0 undefined)
     in D fcost $ HasThunk.thunk t $ \x' -> case f (S 0 x') of
          C _ y -> y
  force (D tcost th) (S scost stack) = C (tcost + scost) (HasThunk.force th stack)

  call g (S kcost k) = C kcost (HasThunk.call g k)

instance Callcc.Callcc t => Callcc.Callcc (MonoInliner t) where
  catch t f =
    let C fcost _ = f (S 0 undefined)
     in C fcost $ Callcc.catch t $ \x' -> case f (S 0 x') of
          C _ y -> y
  throw (S scost stack) (C xcost x) = C (scost + xcost) (Callcc.throw stack x)

instance Cps.Cps t => Cps.Cps (MonoInliner t) where
  nil = S 0 Cps.nil

  letTo t f =
    let C fcost _ = f (D 0 undefined)
     in S fcost $ Cps.letTo t $ \x' -> case f (D 0 x') of
          C _ y -> y

  throw (S tcost stk) (D scost c) = C (tcost + scost) (Cps.throw stk c)

  apply (D xcost x) (S kcost k) = S (xcost + kcost) $ Cps.apply x k

instance HasReturn t => HasReturn (MonoInliner t) where
  returns (D cost k) = C cost (returns k)

instance SystemF.SystemF t => SystemF.SystemF (MonoInliner t) where
  pair (C xcost x) (C ycost y) = C (xcost + ycost) (SystemF.pair x y)
  unpair (C tcost tuple) f =
    let C rcost _ = f (C 0 undefined) (C 0 undefined)
     in C (tcost + rcost) $ SystemF.unpair tuple $ \x y -> case f (C 0 x) (C 0 y) of
          C _ r -> r

  letBe (C xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(C inlineCost _) = f (C 1 x)
      notinlined = C (xcost + fcost) $ SystemF.letBe x $ \x' -> case f (C 0 x') of
        C _ y -> y
      C fcost _ = f (C 0 x)

  lambda t f =
    let C fcost _ = f (C 0 (global (probe t)))
     in C fcost $ SystemF.lambda t $ \x' -> case f (C 0 x') of
          C _ y -> y
  C fcost f <*> C xcost x = C (fcost + xcost) (f SystemF.<*> x)

probe :: SAlgebra a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
