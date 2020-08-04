{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsIntrinsified (Code, Data, AsIntrinsified, extract) where

import Cbpv
import Common
import Core
import GlobalMap (GlobalMap)
import qualified GlobalMap
import HasCall
import HasConstants
import HasLet
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Code cd dta :~> cd
extract = NatTrans $ \(C x) -> x

data AsIntrinsified t

newtype Code (cd :: Algebra -> *) (dta :: Set -> *) a = C {unC :: cd a}

newtype Data (cd :: Algebra -> *) (dta :: Set -> *) a = D {unD :: dta a}

instance Cbpv cd dta => HasCall (Code cd dta) where
  call g = C $ case GlobalMap.lookup g intrinsics of
    Nothing -> call g
    Just intrinsic -> intrinsic

instance HasConstants dta => HasConstants (Data cd dta) where
  constant = D . constant

instance HasTuple cd dta => HasTuple (Code cd dta) (Data cd dta) where
  pair (D x) (D y) = D (pair x y)
  ofPair f = C . ofPair (\x y -> unC $ f (D x) (D y)) . unD

instance HasLet cd dta => HasLet (Code cd dta) (Data cd dta) where
  whereIs f = C . whereIs (unC . f . D) . unD

instance HasReturn cd dta => HasReturn (Code cd dta) (Data cd dta) where
  returns = C . returns . unD
  from f = C . from (unC . f . D) . unC

instance HasFn cd dta => HasFn (Code cd dta) (Data cd dta) where
  C f <*> D x = C (f <*> x)
  lambda t f = C $ lambda t (unC . f . D)

instance HasThunk cd dta => HasThunk (Code cd dta) (Data cd dta) where
  thunk = D . thunk . unC
  force = C . force . unD

intrinsics :: Cbpv cd dta => GlobalMap cd
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus plusIntrinsic
    ]

plusIntrinsic :: Cbpv cd dta => cd ('F 'U64 :-> 'F 'U64 :-> 'F 'U64)
plusIntrinsic = lambda inferSet $ \x' ->
  lambda inferSet $ \y' ->
    force x' `letTo` \x'' ->
      force y' `letTo` \y'' ->
        call strictPlus <*> x'' <*> y''
