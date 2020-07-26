{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (extract, AsCps) where

import Cbpv
import Common
import qualified Constant
import qualified Cps
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple

extract :: Cps.Cps t => Data (AsCps t) a -> Data t a
extract (D _ x) = x

data AsCps t

instance HasCode t => HasCode (AsCps t) where
  data Code (AsCps t) a = C (SAlgebra a) (Stack t a -> Code t 'Void)

instance HasData t => HasData (AsCps t) where
  data Data (AsCps t) a = D (SSet a) (Data t a)

instance HasStack t => HasStack (AsCps t) where
  data Stack (AsCps t) a = S (SAlgebra a) (Stack t a)

instance HasConstants t => HasConstants (AsCps t) where
  constant k = D (Constant.typeOf k) $ constant k

instance HasLet t => HasLet (AsCps t) where
  letBe (D t x) f =
    let C b _ = f (D t x)
     in C b $ \k ->
          letBe x $ \val ->
            case f (D t val) of
              C _ f' -> f' k

instance Cps.Cps t => HasReturn (AsCps t) where
  returns (D t x) = C (SF t) $ \k -> Cps.returns k x
  letTo (C (SF t) x) f =
    let C b _ = f (D t undefined)
     in C b $ \k -> x $ Cps.letTo t $ \val ->
          case f (D t val) of
            C _ f' -> f' k

instance Cps.Cps t => HasTuple (AsCps t) where
  pair (D tx x) (D ty y) = D (SPair tx ty) (pair x y)
  unpair (D (SPair tx ty) tuple) f =
    let C t _ = f (D tx undefined) (D ty undefined)
     in C t $ \k -> unpair tuple $ \x y -> case f (D tx x) (D ty y) of
          C _ result -> result k

instance Cps.HasThunk t => HasThunk (AsCps t) where
  force (D (SU t) thunk) = C t (Cps.force thunk)
  thunk (C t code) = D (SU t) (Cps.thunk t code)

instance Cps.HasFn t => HasFn (AsCps t) where
  apply (C (_ `SFn` b) f) (D _ x) = C b $ \k -> f (Cps.apply x k)
  lambda t f =
    let C bt _ = f (D t undefined)
     in C (t `SFn` bt) $ \k -> Cps.lambda k $ \x next ->
          let C _ body = f (D t x)
           in body next

instance Cps.HasCall t => HasCall (AsCps t) where
  call g@(Global t _) = C t (Cps.call g)
