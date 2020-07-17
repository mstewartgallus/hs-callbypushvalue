{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCallcc (extract, AsCallcc (..)) where

import qualified Callcc
import qualified Cbpv
import Common
import qualified Constant
import Core
import qualified Cps
import Explicit
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import qualified HasThunk
import qualified Pure
import qualified SystemF
import Tuple

extract :: CodeRep (AsCallcc t) a -> CodeRep t a
extract (CodeCallcc _ x) = x

data AsCallcc t

instance HasCode t => HasCode (AsCallcc t) where
  data CodeRep (AsCallcc t) a = CodeCallcc (SAlgebra a) (CodeRep t a)

instance HasData t => HasData (AsCallcc t) where
  data DataRep (AsCallcc t) a = DataCallcc (SSet a) (DataRep t a)

instance Callcc.Callcc t => HasGlobals (AsCallcc t) where
  global g@(Global t _) = CodeCallcc t (Callcc.catch t (HasThunk.call g))

instance HasConstants t => HasConstants (AsCallcc t) where
  constant k = DataCallcc (Constant.typeOf k) $ constant k

instance Pure.Pure t => Pure.Pure (AsCallcc t) where
  pure (DataCallcc t x) = CodeCallcc (SF t) $ Pure.pure x

instance HasLet t => HasLet (AsCallcc t) where
  letBe (DataCallcc t x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ letBe x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body

instance Callcc.Callcc t => Explicit (AsCallcc t) where
  letTo (CodeCallcc (SF t) x) f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc bt $ letTo x $ \x' ->
          let CodeCallcc _ body = f (DataCallcc t x')
           in body
  apply (CodeCallcc (_ `SFn` b) f) (DataCallcc _ x) = CodeCallcc b $ apply f x

instance Tuple t => Tuple (AsCallcc t)

instance Callcc.Callcc t => Cbpv.Cbpv (AsCallcc t) where
  lambda t f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc (t `SFn` bt) $ Callcc.catch (t `SFn` bt) $ \k ->
          HasThunk.lambda k $ \x n ->
            let CodeCallcc _ body = f (DataCallcc t x)
             in Callcc.throw n body
  force (DataCallcc (SU t) thunk) = CodeCallcc t $ Callcc.catch t (HasThunk.force thunk)
  thunk (CodeCallcc t code) = DataCallcc (SU t) $ HasThunk.thunk t $ \x ->
    Callcc.throw x code
