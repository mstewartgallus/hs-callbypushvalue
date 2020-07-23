{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (toContinuationPassingStyle, AsCps) where

import qualified Callcc
import Common
import qualified Constant
import qualified Cps
import HasCode
import HasConstants
import HasData
import HasLet
import HasLetLabel
import HasLetTo
import HasReturn
import HasStack
import HasThunk
import HasTuple

toContinuationPassingStyle :: (HasCode t, Cps.Cps t) => Code (AsCps t) a -> Data t ('U a)
toContinuationPassingStyle (CodeCallcc t x) = HasThunk.thunk t x

data AsCps t

instance HasCode t => HasCode (AsCps t) where
  data Code (AsCps t) a = CodeCallcc (SAlgebra a) (Stack t a -> Code t 'Void)

instance HasData t => HasData (AsCps t) where
  data Data (AsCps t) a = DataCallcc (SSet a) (Data t a)

instance (HasStack t) => HasStack (AsCps t) where
  data Stack (AsCps t) a = SB (SAlgebra a) (Stack t a)

instance (HasData t, HasConstants t) => HasConstants (AsCps t) where
  constant k = DataCallcc (Constant.typeOf k) $ constant k

instance (HasCode t, Cps.Cps t) => HasReturn (AsCps t) where
  returns (DataCallcc t x) = CodeCallcc (SF t) $ \k -> Cps.throw k x

instance (HasLet t) => HasLet (AsCps t) where
  letBe (DataCallcc t x) f =
    let CodeCallcc b _ = f (DataCallcc t x)
     in CodeCallcc b $ \k ->
          letBe x $ \val ->
            case f (DataCallcc t val) of
              CodeCallcc _ f' -> f' k

instance (Cps.Cps t) => HasLetTo (AsCps t) where
  letTo (CodeCallcc (SF t) x) f =
    let CodeCallcc b _ = f (DataCallcc t undefined)
     in CodeCallcc b $ \k ->
          x
            ( Cps.letTo t $ \val ->
                case f (DataCallcc t val) of
                  CodeCallcc _ f' -> f' k
            )
  apply (CodeCallcc (_ `SFn` b) f) (DataCallcc _ x) = CodeCallcc b $ \k -> f (Cps.apply x k)

instance (HasCode t, Cps.Cps t) => HasTuple (AsCps t)

instance (HasThunk t, Cps.Cps t) => HasThunk.HasThunk (AsCps t) where
  lambda s@(SB (xt `SFn` r) lam) f =
    let CodeCallcc ct _ = f (DataCallcc xt undefined) (SB r undefined)
     in CodeCallcc ct $ \k -> HasThunk.lambda lam $ \x t ->
          let CodeCallcc _ y = f (DataCallcc xt x) (SB r t)
           in y k

  thunk t f = DataCallcc (SU t) $ HasThunk.thunk t $ \k ->
    case f (SB t k) of
      CodeCallcc _ y -> y Cps.nil

  force (DataCallcc _ th) (SB _ stack) = CodeCallcc SVoid $ \_ ->
    HasThunk.force th stack

  call g (SB _ k) = CodeCallcc SVoid $ \_ -> HasThunk.call g k

instance Cps.Cps t => Callcc.Callcc (AsCps t) where
  catch t f = CodeCallcc t $ \k -> letLabel k $ \k' ->
    case f (SB t k') of
      CodeCallcc _ y -> y Cps.nil

  throw (SB _ x) (CodeCallcc _ f) = CodeCallcc SVoid $ \_ -> f x
