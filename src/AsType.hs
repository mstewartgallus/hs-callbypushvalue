{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsType (extract, AsType) where

import Cbpv
import Common
import qualified Constant
import qualified Cps
import Global
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple

extract :: Code AsType a -> SAlgebra a
extract (C x) = x

extractData :: Data AsType a -> SSet a
extractData (D x) = x

data AsType

instance HasCode AsType where
  newtype Code AsType a = C (SAlgebra a)

instance HasData AsType where
  newtype Data AsType a = D (SSet a)

instance HasConstants AsType where
  constant k = D (Constant.typeOf k)

instance HasLet AsType where
  letBe (D t) f = f (D t)

instance HasReturn AsType where
  returns (D t) = C (SF t)
  letTo (C (SF t)) f = f (D t)

instance HasTuple AsType where
  pair (D tx) (D ty) = D (SPair tx ty)
  unpair (D (SPair tx ty)) f = f (D tx) (D ty)

instance HasThunk AsType where
  force (D (SU t)) = C t
  thunk (C t) = D (SU t)

instance HasFn AsType where
  C (_ `SFn` b) <*> D x = C b
  lambda t f =
    let C bt = f (D t)
     in C (t `SFn` bt)

instance HasCall AsType where
  call g@(Global t _) = C t
