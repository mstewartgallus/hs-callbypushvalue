{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module MonoInliner (extract, MonoInliner (..)) where

import qualified Callcc
import Cbpv
import Common
import qualified Data.Text as T
import Explicit
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasStack
import qualified HasThunk
import Name
import qualified Pure
import qualified SystemF
import TextShow
import Tuple
import qualified Unique
import Prelude hiding ((<*>))

data MonoInliner t

extract :: CodeRep (MonoInliner t) a -> CodeRep t a
extract (M _ x) = x

instance HasCode t => HasCode (MonoInliner t) where
  data CodeRep (MonoInliner t) a = M Int (CodeRep t a)

instance HasData t => HasData (MonoInliner t) where
  data DataRep (MonoInliner t) a = MS Int (DataRep t a)

instance HasStack t => HasStack (MonoInliner t) where
  data StackRep (MonoInliner t) a = SB Int (StackRep t a)

instance HasGlobals t => HasGlobals (MonoInliner t) where
  global g = M 0 (global g)

instance HasConstants t => HasConstants (MonoInliner t) where
  constant k = MS 0 (constant k)
  unit = MS 0 unit

instance Tuple t => Tuple (MonoInliner t) where
  pair (MS xcost x) (MS ycost y) = MS (xcost + ycost) (pair x y)

instance HasLet t => HasLet (MonoInliner t) where
  letBe (MS xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(M inlineCost _) = f (MS 1 x)
      notinlined = M (xcost + fcost) $ letBe x $ \x' -> case f (MS 0 x') of
        M _ y -> y
      M fcost _ = f (MS 0 x)

instance Explicit t => Explicit (MonoInliner t) where
  letTo (M xcost x) f =
    let -- fixme... figure out a better probe...
        M fcost _ = f (MS 0 undefined)
     in M (xcost + fcost) $ letTo x $ \x' -> case f (MS 0 x') of
          M _ y -> y

  lambda t f =
    let M fcost _ = f (MS 0 undefined)
     in M fcost $ lambda t $ \x' -> case f (MS 0 x') of
          M _ y -> y

  apply (M fcost f) (MS xcost x) = M (fcost + xcost) (apply f x)

instance Cbpv t => Cbpv (MonoInliner t) where
  force (MS cost thunk) = M cost (force thunk)
  thunk (M cost code) = MS cost (thunk code)

instance HasThunk.HasThunk t => HasThunk.HasThunk (MonoInliner t) where
  thunk t f =
    let M fcost _ = f (SB 0 undefined)
     in MS fcost $ HasThunk.thunk t $ \x' -> case f (SB 0 x') of
          M _ y -> y
  force (MS tcost thunk) (SB scost stack) = M (tcost + scost) (HasThunk.force thunk stack)

instance Callcc.Callcc t => Callcc.Callcc (MonoInliner t) where
  catch t f =
    let M fcost _ = f (SB 0 undefined)
     in M fcost $ Callcc.catch t $ \x' -> case f (SB 0 x') of
          M _ y -> y
  throw (SB scost stack) (M xcost x) = M (scost + xcost) (Callcc.throw stack x)

instance Pure.Pure t => Pure.Pure (MonoInliner t) where
  pure (MS cost k) = M cost (Pure.pure k)

instance SystemF.SystemF t => SystemF.SystemF (MonoInliner t) where
  pair (M xcost x) (M ycost y) = M (xcost + ycost) (SystemF.pair x y)

  letBe (M xcost x) f = result
    where
      result
        | inlineCost <= 1 = inlined
        | otherwise = notinlined
      inlined@(M inlineCost _) = f (M 1 x)
      notinlined = M (xcost + fcost) $ SystemF.letBe x $ \x' -> case f (M 0 x') of
        M _ y -> y
      M fcost _ = f (M 0 x)

  lambda t f =
    let M fcost _ = f (M 0 (global (probe t)))
     in M fcost $ SystemF.lambda t $ \x' -> case f (M 0 x') of
          M _ y -> y
  M fcost f <*> M xcost x = M (fcost + xcost) (f SystemF.<*> x)

probe :: SAlgebra a -> Global a
probe t = Global t $ Name (T.pack "core") (T.pack "probe")
