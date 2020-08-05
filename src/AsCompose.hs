{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCompose ((:.:), extract, extractData, extractStack) where

import Cbpv
import Common
import Control.Category
import qualified Cps
import qualified Cps
import Global
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import NatTrans
import PairF
import qualified Path
import SystemF (SystemF)
import qualified SystemF as F
import qualified Unique
import Prelude hiding ((.), (<*>))

extract :: Code (AsCompose f g x) :~> Code (f (g x))
extract = NatTrans $ \(C x) -> x

extractData :: Data (AsCompose f g x) :~> Data (f (g x))
extractData = NatTrans $ \(D x) -> x

extractStack :: Stack (AsCompose f g x) :~> Stack (f (g x))
extractStack = NatTrans $ \(S x) -> x

type (:.:) = AsCompose

infixr 0 :.:

data AsCompose (f :: * -> *) (g :: * -> *) x

instance HasCode (AsCompose f g x) where
  newtype Code (AsCompose f g x) a = C {unC :: Code (f (g x)) a}

instance HasData (AsCompose f g x) where
  newtype Data (AsCompose f g x) a = D (Data (f (g x)) a)

instance HasStack (AsCompose f g x) where
  newtype Stack (AsCompose f g x) a = S (Stack (f (g x)) a)

instance HasCall (f (g x)) => HasCall (AsCompose f g x) where
  call = C . call

instance Cps.HasCall (f (g x)) => Cps.HasCall (AsCompose f g x) where
  call = D . Cps.call

instance F.HasConstants (f (g x)) => F.HasConstants (AsCompose f g x) where
  constant = C . F.constant

instance HasConstants (f (g x)) => HasConstants (AsCompose f g x) where
  constant = D . constant

instance F.HasLet (f (g x)) => F.HasLet (AsCompose f g x) where
  whereIs f (C x) = C $ F.letBe x $ \x' -> case f (C x') of
    C y -> y

instance HasLet (f (g x)) => HasLet (AsCompose f g x) where
  whereIs f (D x) = C $ letBe x $ \x' -> case f (D x') of
    C y -> y

instance Cps.HasLabel (f (g x)) => Cps.HasLabel (AsCompose f g x) where
  label (S x) f = C $ Cps.label x $ \x' -> case f (S x') of
    C y -> y

instance HasThunk (f (g x)) => HasThunk (AsCompose f g x) where
  thunk (C x) = D (thunk x)
  force (D x) = C (force x)

instance HasReturn (f (g x)) => HasReturn (AsCompose f g x) where
  returns (D x) = C (returns x)
  from f (C x) = C $ letTo x $ \x' -> case f (D x') of
    C y -> y

instance F.HasTuple (f (g x)) => F.HasTuple (AsCompose f g x)

instance HasTuple (f (g x)) => HasTuple (AsCompose f g x)

instance Cps.HasReturn (f (g x)) => Cps.HasReturn (AsCompose f g x) where
  returns (D x) (S k) = C (Cps.returns x k)
  letTo t f = S $ Cps.letTo t $ \x -> case f (D x) of
    C y -> y

instance Cps.HasThunk (f (g x)) => Cps.HasThunk (AsCompose f g x) where
  force (D x) (S k) = C (Cps.force x k)
  thunk t f = D $ Cps.thunk t $ \x -> case f (S x) of
    C y -> y

instance F.HasFn (f (g x)) => F.HasFn (AsCompose f g x) where
  lambda t f = C $ F.lambda t (Path.make unC . f . Path.make C)
  C f <*> C x = C (f F.<*> x)

instance Cps.HasFn (f (g x)) => Cps.HasFn (AsCompose f g x) where
  lambda (S k) f = C $ Cps.lambda k $ \x n -> case f (D x) (S n) of
    C y -> y

  D f <*> S x = S (f Cps.<*> x)

instance HasFn (f (g x)) => HasFn (AsCompose f g x) where
  lambda t f = C $ lambda t $ \x -> case f (D x) of
    C y -> y
  C f <*> D x = C (f <*> x)
