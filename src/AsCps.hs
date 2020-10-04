{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (extract, AsCps) where

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
import HasTerminal
import HasTuple
import NatTrans

extract :: Cps.Cps t => Data (AsCps t) :~> Data t
extract = NatTrans $ \(D _ x) -> x

data AsCps t

instance HasCode t => HasCode (AsCps t) where
  data Code (AsCps t) a = C (SAlgebra a) (Stack t a -> Code t Void)

instance HasData t => HasData (AsCps t) where
  data Data (AsCps t) a = D (SSet a) (Data t a)

instance HasConstants t => HasConstants (AsCps t) where
  constant k = D (SU (fromType (Constant.typeOf k))) $ constant k

instance HasTerminal t => HasTerminal (AsCps t) where
  terminal = D SUnit terminal

instance HasLet t => HasLet (AsCps t) where
  letBe (D t x) f =
    let C b _ = f (D t x)
     in C b $ \k ->
          letBe x $ \val ->
            case f (D t val) of
              C _ f' -> f' k

instance Cps.Cps t => HasReturn (AsCps t) where
  returns (D t x) = C (SF t) (Cps.returns x)
  letTo (C (SF t) x) f =
    let C b _ = f (D t undefined)
     in C b $ \k -> x $
          Cps.letTo t $ \val ->
            case f (D t val) of
              C _ f' -> f' k

instance Cps.Cps t => HasTuple (AsCps t)

instance Cps.HasThunk t => HasThunk (AsCps t) where
  force (D (SU t) th) = C t (Cps.force th)
  thunk (C t code) = D (SU t) (Cps.thunk t code)

instance Cps.HasFn t => HasFn (AsCps t) where
  C (_ `SFn` b) f <*> D _ x = C b $ \k -> f (x Cps.<*> k)
  lambda t f =
    let C bt _ = f (D t undefined)
     in C (t `SFn` bt) $ \k -> Cps.lambda k $ \x next ->
          let C _ body = f (D t x)
           in body next

instance (Cps.HasThunk t, Cps.HasCall t) => HasCall (AsCps t) where
  call g@(Global t _) = C (fromType t) (\k -> Cps.force (Cps.call g) k)
