{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (extract, AsCps) where

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

extract :: Cps.Cps t => Data (AsCps t) a -> Data t a
extract (D _ x) = x

data AsCps t

instance HasCode t => HasCode (AsCps t) where
  data Code (AsCps t) a = C (SAlgebra a) (Stack t a -> Code t 'Void)

instance HasData t => HasData (AsCps t) where
  data Data (AsCps t) a = D (SSet a) (Data t a)

instance (HasStack t) => HasStack (AsCps t) where
  data Stack (AsCps t) a = S (SAlgebra a) (Stack t a)

instance (HasData t, HasConstants t) => HasConstants (AsCps t) where
  unit = D SUnit unit
  constant k = D (Constant.typeOf k) $ constant k

instance (HasCode t, Cps.Cps t) => HasReturn (AsCps t) where
  returns (D t x) = C (SF t) $ \k -> Cps.throw k x

instance (HasLet t) => HasLet (AsCps t) where
  letBe (D t x) f =
    let C b _ = f (D t x)
     in C b $ \k ->
          letBe x $ \val ->
            case f (D t val) of
              C _ f' -> f' k

instance (Cps.Cps t) => HasLetTo (AsCps t) where
  letTo (C (SF t) x) f =
    let C b _ = f (D t undefined)
     in C b $ \k ->
          x
            ( Cps.letTo t $ \val ->
                case f (D t val) of
                  C _ f' -> f' k
            )
  apply (C (_ `SFn` b) f) (D _ x) = C b $ \k -> f (Cps.apply x k)

instance (HasCode t, Cps.Cps t) => HasTuple (AsCps t) where
  pair (D tx x) (D ty y) = D (SPair tx ty) (pair x y)

instance (HasThunk t, Cps.Cps t) => HasThunk.HasThunk (AsCps t) where
  lambda s@(S (xt `SFn` r) lam) f =
    let C ct _ = f (D xt undefined) (S r undefined)
     in C ct $ \k -> HasThunk.lambda lam $ \x t ->
          let C _ y = f (D xt x) (S r t)
           in y k

  thunk t f = D (SU t) $ HasThunk.thunk t $ \k ->
    case f (S t k) of
      C _ y -> y Cps.nil

  force (D _ th) (S _ stack) = C SVoid $ \_ ->
    HasThunk.force th stack

  call g (S _ k) = C SVoid $ \_ -> HasThunk.call g k

instance Cps.Cps t => Callcc.Callcc (AsCps t) where
  catch t f = C t $ \k -> letLabel k $ \k' ->
    case f (S t k') of
      C _ y -> y Cps.nil

  throw (S _ x) (C _ f) = C SVoid $ \_ -> f x
