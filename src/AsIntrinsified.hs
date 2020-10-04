{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsIntrinsified (AsIntrinsified, extract, Code (..), Data (..)) where

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
import HasTerminal
import HasTuple
import NatTrans
import Prelude hiding ((<*>))

extract :: Cbpv t => Code (AsIntrinsified t) :~> Code t
extract = NatTrans unC

newtype AsIntrinsified t = AsIntrinsified t deriving (HasConstants, HasTuple, HasTerminal, HasLet, HasReturn, HasFn, HasThunk)

instance HasCode t => HasCode (AsIntrinsified t) where
  newtype Code (AsIntrinsified t) a = C {unC :: Code t a}

instance HasData t => HasData (AsIntrinsified t) where
  newtype Data (AsIntrinsified t) a = D {unD :: Data t a}

instance Cbpv t => HasCall (AsIntrinsified t) where
  call g = C $ case GlobalMap.lookup g intrinsics of
    Nothing -> call g
    Just (G intrinsic) -> intrinsic

newtype G t a = G (Code t (FromType a))

intrinsics :: Cbpv t => GlobalMap (G t)
intrinsics =
  GlobalMap.fromList
    []

-- GlobalMap.Entry plus (G plusIntrinsic)

-- plusIntrinsic :: Cbpv t => Code t (U (F U64) ~> U (F U64) ~> F U64)
-- plusIntrinsic = lambda inferSet $ \x' ->
--   lambda inferSet $ \y' ->
--     force x' `letTo` \x'' ->
--       force y' `letTo` \y'' ->
--         call strictPlus <*> x'' <*> y''
