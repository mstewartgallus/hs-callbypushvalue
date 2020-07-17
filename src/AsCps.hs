{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (toContinuationPassingStyle) where

import qualified Callcc
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
import HasLetLabel
import HasStack
import HasThunk
import qualified Pure
import Tuple

toContinuationPassingStyle :: (HasCode t, Cps.Cps t) => Callcc.Code a -> DataRep t (U a)
toContinuationPassingStyle code = case Callcc.abstractCode code of
  CodeCallcc t x -> HasThunk.thunk t x

data AsCps t

instance HasCode t => HasCode (AsCps t) where
  data CodeRep (AsCps t) a = CodeCallcc (SAlgebra a) (StackRep t a -> CodeRep t Void)

instance HasData t => HasData (AsCps t) where
  data DataRep (AsCps t) a = DataCallcc (SSet a) (DataRep t a)

instance (HasStack t) => HasStack (AsCps t) where
  data StackRep (AsCps t) a = SB (SAlgebra a) (StackRep t a)

instance (HasData t, HasConstants t) => HasConstants (AsCps t) where
  constant k = DataCallcc (Constant.typeOf k) $ constant k

instance (HasCode t, Cps.Cps t) => Pure.Pure (AsCps t) where
  pure (DataCallcc t x) = CodeCallcc (SF t) $ \k -> Cps.throw k x

instance (HasLet t) => HasLet (AsCps t) where
  letBe (DataCallcc t x) f =
    let CodeCallcc b _ = f (DataCallcc t x)
     in CodeCallcc b $ \k ->
          letBe x $ \val ->
            case f (DataCallcc t val) of
              CodeCallcc _ f' -> f' k

instance (Cps.Cps t) => Explicit (AsCps t) where
  letTo (CodeCallcc (SF t) x) f =
    let CodeCallcc b _ = f (DataCallcc t undefined)
     in CodeCallcc b $ \k ->
          x
            ( Cps.letTo t $ \val ->
                case f (DataCallcc t val) of
                  CodeCallcc _ f' -> f' k
            )
  apply (CodeCallcc (_ `SFn` b) f) (DataCallcc _ x) = CodeCallcc b $ \k -> f (Cps.apply x k)

instance (HasCode t, Cps.Cps t) => Tuple (AsCps t)

instance (HasThunk t, Cps.Cps t) => HasThunk.HasThunk (AsCps t) where
  lambda s@(SB (xt `SFn` r) lam) f =
    let CodeCallcc ct _ = f (DataCallcc xt undefined) (SB r undefined)
     in CodeCallcc ct $ \k -> HasThunk.lambda lam $ \x t ->
          let CodeCallcc _ y = f (DataCallcc xt x) (SB r t)
           in y k

  thunk t f = DataCallcc (SU t) $ HasThunk.thunk t $ \k ->
    case f (SB t k) of
      CodeCallcc _ y -> y Cps.nil

  force (DataCallcc _ thunk) (SB _ stack) = CodeCallcc SVoid $ \_ ->
    HasThunk.force thunk stack

  call g (SB _ k) = CodeCallcc SVoid $ \_ -> HasThunk.call g k

instance (HasLetLabel t, Cps.Cps t) => Callcc.Callcc (AsCps t) where
  catch t f = CodeCallcc t $ \k -> letLabel k $ \k' ->
    case f (SB t k') of
      CodeCallcc _ y -> y Cps.nil

  throw (SB _ x) (CodeCallcc _ f) = CodeCallcc SVoid $ \_ -> f x
