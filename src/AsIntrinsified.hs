{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsIntrinsified (AsIntrinsified, extract) where

import Cbpv
import Common
import Core
import GlobalMap (GlobalMap)
import qualified GlobalMap
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Cbpv t => Code (AsIntrinsified t) :~> Code t
extract = NatTrans $ \(C x) -> x

data AsIntrinsified t

instance HasCode t => HasCode (AsIntrinsified t) where
  newtype Code (AsIntrinsified t) a = C {unC :: Code t a}

instance HasData t => HasData (AsIntrinsified t) where
  newtype Data (AsIntrinsified t) a = D {unD :: Data t a}

instance Cbpv t => HasCall (AsIntrinsified t) where
  call g = C $ case GlobalMap.lookup g intrinsics of
    Nothing -> call g
    Just intrinsic -> intrinsic

instance HasConstants t => HasConstants (AsIntrinsified t) where
  constant = D . constant

instance Cbpv t => HasTuple (AsIntrinsified t) where
  pair (D x) (D y) = D (pair x y)
  unpair (D tuple) f = C $ unpair tuple $ \x y ->
    unC $ f (D x) (D y)

instance HasLet t => HasLet (AsIntrinsified t) where
  whereIs f = C . whereIs (unC . f . D) . unD

instance HasReturn t => HasReturn (AsIntrinsified t) where
  returns = C . returns . unD
  from f = C . from (unC . f . D) . unC

instance HasFn t => HasFn (AsIntrinsified t) where
  C f <*> D x = C (f <*> x)
  lambda t f = C $ lambda t (unC . f . D)

instance HasThunk t => HasThunk (AsIntrinsified t) where
  thunk = D . thunk . unC
  force = C . force . unD

intrinsics :: Cbpv t => GlobalMap (Code t)
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus plusIntrinsic
    ]

plusIntrinsic :: Cbpv t => Code t ('F 'U64 :-> 'F 'U64 :-> 'F 'U64)
plusIntrinsic = lambda inferSet $ \x' ->
  lambda inferSet $ \y' ->
    force x' `letTo` \x'' ->
      force y' `letTo` \y'' ->
        call strictPlus <*> x'' <*> y''
