{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCallcc (extract, AsCallcc) where

import qualified Callcc
import qualified Cbpv
import Cbpv (HasFn (..), HasGlobals (..), HasReturn (..), HasThunk (..))
import Common
import qualified Constant
import qualified Cps
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple

extract :: Data (AsCallcc t) a -> Data t a
extract (D _ x) = x

data AsCallcc t

instance HasCode t => HasCode (AsCallcc t) where
  data Code (AsCallcc t) a = C (SAlgebra a) (Code t a)

instance HasData t => HasData (AsCallcc t) where
  data Data (AsCallcc t) a = D (SSet a) (Data t a)

instance HasGlobals t => HasGlobals (AsCallcc t) where
  global g@(Global t _) = C t (global g)

instance HasConstants t => HasConstants (AsCallcc t) where
  unit = D SUnit unit
  constant k = D (Constant.typeOf k) $ constant k

instance HasLet t => HasLet (AsCallcc t) where
  letBe (D t x) f =
    let C bt _ = f (D t undefined)
     in C bt $ letBe x $ \x' ->
          let C _ body = f (D t x')
           in body

instance Callcc.Callcc t => HasReturn (AsCallcc t) where
  returns (D t x) = C (SF t) $ returns x
  letTo (C (SF t) x) f =
    let C bt _ = f (D t undefined)
     in C bt $ letTo x $ \x' ->
          let C _ body = f (D t x')
           in body

instance HasTuple t => HasTuple (AsCallcc t) where
  pair (D tx x) (D ty y) = D (SPair tx ty) (pair x y)

  unpair (D (SPair tx ty) tuple) f =
    let C t _ = f (D tx undefined) (D ty undefined)
     in C t $ unpair tuple $ \x y -> case f (D tx x) (D ty y) of
          C _ result -> result

instance HasFn t => HasFn (AsCallcc t) where
  apply (C (_ `SFn` b) f) (D _ x) = C b $ apply f x
  lambda t f =
    let C bt _ = f (D t undefined)
     in C (t `SFn` bt) $ lambda t $ \x ->
          let C _ body = f (D t x)
           in body

instance Callcc.Callcc t => HasThunk (AsCallcc t) where
  force (D (SU t) thunk) = C t $ Callcc.catch t (Cps.force thunk)
  thunk (C t code) = D (SU t) $ Cps.thunk t $ \x ->
    Callcc.throw x code
