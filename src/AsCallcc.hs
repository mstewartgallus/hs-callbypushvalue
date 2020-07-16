{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCallcc (extract, AsCallcc (..)) where

import Basic
import qualified Callcc
import qualified Cbpv
import Common
import Const
import qualified Constant
import Core
import qualified Cps
import Explicit
import Global
import qualified Pure
import qualified SystemF
import Tuple

extract :: AlgRep (AsCallcc t) a -> AlgRep t a
extract (CodeCallcc _ x) = x

data AsCallcc t

instance Basic t => Basic (AsCallcc t) where
  data AlgRep (AsCallcc t) a = CodeCallcc (SAlg a) (AlgRep t a)
  global g@(Global t _) = CodeCallcc t (global g)

instance Const t => Const (AsCallcc t) where
  data SetRep (AsCallcc t) a = DataCallcc (SSet a) (SetRep t a)
  constant k = DataCallcc (Constant.typeOf k) $ constant k

instance Pure.Pure t => Pure.Pure (AsCallcc t) where
  pure (DataCallcc t x) = CodeCallcc (SF t) $ Pure.pure x

instance Explicit t => Explicit (AsCallcc t) where
  letBe (DataCallcc t x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ letBe x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  letTo (CodeCallcc (SF t) x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ letTo x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  lambda t f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc (t `SFn` bt) $ lambda t $ \x ->
          let CodeCallcc _ body = f (DataCallcc t x)
           in body
  apply (CodeCallcc (_ `SFn` b) f) (DataCallcc _ x) = CodeCallcc b $ apply f x

instance Tuple t => Tuple (AsCallcc t)

instance Callcc.Callcc t => Cbpv.Cbpv (AsCallcc t) where
  force (DataCallcc (SU t) thunk) = CodeCallcc t $ Callcc.catch t (Callcc.force thunk)
  thunk (CodeCallcc t code) = DataCallcc (SU t) $ Callcc.thunk t $ \x ->
    Callcc.throw x code
