{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsIntrinsified (Intrinsify, extract) where

import Cbpv
import Common
import Constant
import Core
import Explicit
import GlobalMap (GlobalMap)
import qualified GlobalMap
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasReturn
import Tuple
import qualified Unique

extract :: Cbpv t => CodeRep (Intrinsify t) a -> CodeRep t a
extract (I x) = x

data Intrinsify t

instance HasCode t => HasCode (Intrinsify t) where
  newtype CodeRep (Intrinsify t) a = I (CodeRep t a)

instance HasData t => HasData (Intrinsify t) where
  newtype DataRep (Intrinsify t) a = IS (DataRep t a)

instance Cbpv t => HasGlobals (Intrinsify t) where
  global g = I $ case GlobalMap.lookup g intrinsics of
    Nothing -> global g
    Just intrinsic -> intrinsic

instance HasConstants t => HasConstants (Intrinsify t) where
  constant k = IS (constant k)
  unit = IS unit

instance Cbpv t => Tuple (Intrinsify t) where
  pair (IS x) (IS y) = IS (pair x y)
  unpair (IS tuple) f = I $ unpair tuple $ \x y ->
    let I result = f (IS x) (IS y)
     in result

instance Cbpv t => HasReturn (Intrinsify t) where
  returns (IS x) = I (returns x)

instance HasLet t => HasLet (Intrinsify t) where
  letBe (IS x) f = I $ letBe x $ \x' ->
    let I body = f (IS x')
     in body

instance Cbpv t => Explicit (Intrinsify t) where
  letTo (I x) f = I $ letTo x $ \x' ->
    let I body = f (IS x')
     in body
  apply (I f) (IS x) = I (apply f x)

instance Cbpv t => Cbpv (Intrinsify t) where
  lambda t f = I $ lambda t $ \x ->
    let I body = f (IS x)
     in body
  thunk (I x) = IS (thunk x)
  force (IS x) = I (force x)

intrinsics :: Cbpv t => GlobalMap (CodeRep t)
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus plusIntrinsic
    ]

plusIntrinsic :: Cbpv t => CodeRep t (F U64 :-> F U64 :-> F U64)
plusIntrinsic = lambda (SU (SF SU64)) $ \x' ->
  lambda (SU (SF SU64)) $ \y' ->
    letTo (force x') $ \x'' ->
      letTo (force y') $ \y'' ->
        apply (apply (global strictPlus) x'') y''
