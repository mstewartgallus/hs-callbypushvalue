{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (Code, Data, extract) where

import Cbpv
import Common
import qualified Constant
import qualified Cps
import Global
import HasCall
import HasConstants
import HasLet
import HasTuple
import NatTrans

extract :: Data cd dta k :~> dta
extract = NatTrans $ \(D _ x) -> x

data Code cd (dta :: Set -> *) k a = C (SAlgebra a) (k a -> cd 'Void)

data Data (cd :: Algebra -> *) dta (k :: Algebra -> *) a = D (SSet a) (dta a)

instance HasConstants dta => HasConstants (Data cd dta k) where
  constant k = D (Constant.typeOf k) $ constant k

instance HasLet cd dta => HasLet (Code cd dta k) (Data cd dta k) where
  letBe (D t x) f =
    let C b _ = f (D t x)
     in C b $ \k ->
          letBe x $ \val ->
            case f (D t val) of
              C _ f' -> f' k

instance Cps.Cps cd dta k => HasReturn (Code cd dta k) (Data cd dta k) where
  returns (D t x) = C (SF t) (Cps.returns x)
  letTo (C (SF t) x) f =
    let C b _ = f (D t undefined)
     in C b $ \k -> x $ Cps.letTo t $ \val ->
          case f (D t val) of
            C _ f' -> f' k

instance Cps.Cps cd dta k => HasTuple (Code cd dta k) (Data cd dta k) where
  pair (D tx x) (D ty y) = D (SPair tx ty) (pair x y)
  unpair (D (SPair tx ty) tuple) f =
    let C t _ = f (D tx undefined) (D ty undefined)
     in C t $ \k -> unpair tuple $ \x y -> case f (D tx x) (D ty y) of
          C _ result -> result k

instance Cps.HasThunk cd dta k => HasThunk (Code cd dta k) (Data cd dta k) where
  force (D (SU t) th) = C t (Cps.force th)
  thunk (C t code) = D (SU t) (Cps.thunk t code)

instance Cps.HasFn cd dta k => HasFn (Code cd dta k) (Data cd dta k) where
  C (_ `SFn` b) f <*> D _ x = C b $ \k -> f (x Cps.<*> k)
  lambda t f =
    let C bt _ = f (D t undefined)
     in C (t `SFn` bt) $ \k -> Cps.lambda k $ \x next ->
          let C _ body = f (D t x)
           in body next

instance (Cps.HasThunk cd dta k, Cps.HasCall dta) => HasCall (Code cd dta k) where
  call g@(Global t _) = C t (\k -> Cps.force (Cps.call g) k)
