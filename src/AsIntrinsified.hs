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
import Prelude hiding ((<*>))

extract :: Cbpv t => Code (AsIntrinsified t) a -> Code t a
extract (C x) = x

data AsIntrinsified t

instance HasCode t => HasCode (AsIntrinsified t) where
  newtype Code (AsIntrinsified t) a = C (Code t a)

instance HasData t => HasData (AsIntrinsified t) where
  newtype Data (AsIntrinsified t) a = D (Data t a)

instance Cbpv t => HasCall (AsIntrinsified t) where
  call g = C $ case GlobalMap.lookup g intrinsics of
    Nothing -> call g
    Just intrinsic -> intrinsic

instance HasConstants t => HasConstants (AsIntrinsified t) where
  constant k = D (constant k)

instance Cbpv t => HasTuple (AsIntrinsified t) where
  pair (D x) (D y) = D (pair x y)
  unpair (D tuple) f = C $ unpair tuple $ \x y ->
    let C result = f (D x) (D y)
     in result

instance HasLet t => HasLet (AsIntrinsified t) where
  letBe (D x) f = C $ letBe x $ \x' ->
    let C body = f (D x')
     in body

instance HasReturn t => HasReturn (AsIntrinsified t) where
  returns (D x) = C (returns x)
  letTo (C x) f = C $ letTo x $ \x' ->
    let C body = f (D x')
     in body

instance HasFn t => HasFn (AsIntrinsified t) where
  C f <*> D x = C (f <*> x)
  lambda t f = C $ lambda t $ \x ->
    let C body = f (D x)
     in body

instance HasThunk t => HasThunk (AsIntrinsified t) where
  thunk (C x) = D (thunk x)
  force (D x) = C (force x)

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
