{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Intrinsify (intrinsify) where

import Basic
import Cbpv
import Common
import Const
import Constant
import Core
import Data.Text
import Explicit
import GlobalMap (GlobalMap)
import qualified GlobalMap
import TextShow
import Tuple
import Type
import qualified Unique

intrinsify :: Cbpv t => Code a -> AlgRep t a
intrinsify code = case abstractCode code of
  I x -> abstractCode (build x)

data Intrinsify t

instance Cbpv t => Basic (Intrinsify t) where
  newtype AlgRep (Intrinsify t) a = I (AlgRep t a)
  global g = I $ case GlobalMap.lookup g intrinsics of
    Nothing -> global g
    Just intrinsic -> intrinsic

instance Const t => Const (Intrinsify t) where
  newtype SetRep (Intrinsify t) a = IS (SetRep t a)
  constant k = IS (constant k)
  unit = IS unit

instance Tuple t => Tuple (Intrinsify t) where
  pair (IS x) (IS y) = IS (pair x y)
  first (IS tuple) = IS (first tuple)
  second (IS tuple) = IS (second tuple)

instance Cbpv t => Explicit (Intrinsify t) where
  returns (IS x) = I (returns x)

  letTo (I x) f = I $ letTo x $ \x' ->
    let I body = f (IS x')
     in body
  letBe (IS x) f = I $ letBe x $ \x' ->
    let I body = f (IS x')
     in body

  lambda t f = I $ lambda t $ \x ->
    let I body = f (IS x)
     in body
  apply (I f) (IS x) = I (apply f x)

instance Cbpv t => Cbpv (Intrinsify t) where
  thunk (I x) = IS (thunk x)
  force (IS x) = I (force x)

intrinsics :: Cbpv t => GlobalMap (AlgRep t)
intrinsics =
  GlobalMap.fromList
    [ GlobalMap.Entry plus plusIntrinsic
    ]

plusIntrinsic :: Cbpv t => AlgRep t (F U64 :-> F U64 :-> F U64)
plusIntrinsic = lambda (SU (SF SU64)) $ \x' ->
  lambda (SU (SF SU64)) $ \y' ->
    letTo (force x') $ \x'' ->
      letTo (force y') $ \y'' ->
        apply (apply (global strictPlus) x'') y''
