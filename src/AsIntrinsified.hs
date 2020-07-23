{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsIntrinsified (Intrinsify, extract) where

import Cbpv
import Common
import Core
import GlobalMap (GlobalMap)
import qualified GlobalMap
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetTo
import HasReturn
import HasTuple

extract :: Cbpv t => Data (Intrinsify t) a -> Data t a
extract (D x) = x

data Intrinsify t

instance HasCode t => HasCode (Intrinsify t) where
  newtype Code (Intrinsify t) a = C (Code t a)

instance HasData t => HasData (Intrinsify t) where
  newtype Data (Intrinsify t) a = D (Data t a)

instance Cbpv t => HasGlobals (Intrinsify t) where
  global g = C $ case GlobalMap.lookup g intrinsics of
    Nothing -> global g
    Just intrinsic -> intrinsic

instance HasConstants t => HasConstants (Intrinsify t) where
  constant k = D (constant k)
  unit = D unit

instance Cbpv t => HasTuple (Intrinsify t) where
  pair (D x) (D y) = D (pair x y)
  unpair (D tuple) f = C $ unpair tuple $ \x y ->
    let C result = f (D x) (D y)
     in result

instance Cbpv t => HasReturn (Intrinsify t) where
  returns (D x) = C (returns x)

instance HasLet t => HasLet (Intrinsify t) where
  letBe (D x) f = C $ letBe x $ \x' ->
    let C body = f (D x')
     in body

instance Cbpv t => HasLetTo (Intrinsify t) where
  letTo (C x) f = C $ letTo x $ \x' ->
    let C body = f (D x')
     in body
  apply (C f) (D x) = C (apply f x)

instance Cbpv t => Cbpv (Intrinsify t) where
  lambda t f = C $ lambda t $ \x ->
    let C body = f (D x)
     in body
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
    letTo (force x') $ \x'' ->
      letTo (force y') $ \y'' ->
        apply (apply (global strictPlus) x'') y''
