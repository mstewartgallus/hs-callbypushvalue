{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsIntrinsified (Intrinsify, extract) where

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

extract :: Cbpv t => Data (Intrinsify t) a -> Data t a
extract (D x) = x

data Intrinsify t

instance HasCode t => HasCode (Intrinsify t) where
  newtype Code (Intrinsify t) a = C (Code t a)

instance HasData t => HasData (Intrinsify t) where
  newtype Data (Intrinsify t) a = D (Data t a)

instance Cbpv t => HasCall (Intrinsify t) where
  call g = C $ case GlobalMap.lookup g intrinsics of
    Nothing -> call g
    Just intrinsic -> intrinsic

instance HasConstants t => HasConstants (Intrinsify t) where
  constant k = D (constant k)

instance Cbpv t => HasTuple (Intrinsify t) where
  pair (D x) (D y) = D (pair x y)
  unpair (D tuple) f = C $ unpair tuple $ \x y ->
    let C result = f (D x) (D y)
     in result

instance HasLet t => HasLet (Intrinsify t) where
  letBe (D x) f = C $ letBe x $ \x' ->
    let C body = f (D x')
     in body

instance HasReturn t => HasReturn (Intrinsify t) where
  returns (D x) = C (returns x)
  letTo (C x) f = C $ letTo x $ \x' ->
    let C body = f (D x')
     in body

instance HasFn t => HasFn (Intrinsify t) where
  C f <*> D x = C (f <*> x)
  lambda t f = C $ lambda t $ \x ->
    let C body = f (D x)
     in body

instance HasThunk t => HasThunk (Intrinsify t) where
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
