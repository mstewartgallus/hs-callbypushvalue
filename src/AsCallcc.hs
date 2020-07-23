{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCallcc (extract, AsCallcc (..)) where

import qualified Callcc
import qualified Cbpv
import Common
import qualified Constant
import Core
import qualified Cps
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import qualified HasThunk
import HasTuple
import qualified SystemF

extract :: Data (AsCallcc t) a -> Data t a
extract (D _ x) = x

data AsCallcc t

instance HasCode t => HasCode (AsCallcc t) where
  data Code (AsCallcc t) a = C (SAlgebra a) (Code t a)

instance HasData t => HasData (AsCallcc t) where
  data Data (AsCallcc t) a = D (SSet a) (Data t a)

instance Callcc.Callcc t => HasGlobals (AsCallcc t) where
  global g@(Global t _) = C t (Callcc.catch t (HasThunk.call g))

instance HasConstants t => HasConstants (AsCallcc t) where
  constant k = D (Constant.typeOf k) $ constant k

instance HasReturn t => HasReturn (AsCallcc t) where
  returns (D t x) = C (SF t) $ returns x

instance HasLet t => HasLet (AsCallcc t) where
  letBe (D t x) f =
    let C bt _ = f (D t undefined)
     in C bt $ letBe x $ \x' ->
          let C _ body = f (D t x')
           in body

instance Callcc.Callcc t => HasLetTo (AsCallcc t) where
  letTo (C (SF t) x) f =
    let C bt _ = f (D t undefined)
     in C bt $ letTo x $ \x' ->
          let C _ body = f (D t x')
           in body
  apply (C (_ `SFn` b) f) (D _ x) = C b $ apply f x

instance HasTuple t => HasTuple (AsCallcc t)

instance Callcc.Callcc t => Cbpv.Cbpv (AsCallcc t) where
  lambda t f =
    let C bt _ = f (D t undefined)
     in C (t `SFn` bt) $ Callcc.catch (t `SFn` bt) $ \k ->
          HasThunk.lambda k $ \x n ->
            let C _ body = f (D t x)
             in Callcc.throw n body
  force (D (SU t) thunk) = C t $ Callcc.catch t (HasThunk.force thunk)
  thunk (C t code) = D (SU t) $ HasThunk.thunk t $ \x ->
    Callcc.throw x code
