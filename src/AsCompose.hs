{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

newtype AsCompose (f :: * -> *) (g :: * -> *) x = AsCompose (f (g x))
  deriving
    ( HasCall,
      Cps.HasCall,
      F.HasConstants,
      F.HasLet,
      F.HasTuple,
      HasConstants,
      HasLet,
      HasFn,
      HasThunk,
      HasReturn,
      HasTuple,
      Cps.HasLabel,
      Cps.HasThunk,
      Cps.HasReturn,
      Cps.HasFn
    )

instance HasCode (AsCompose f g x) where
  newtype Code (AsCompose f g x) a = C {unC :: Code (f (g x)) a}

instance HasData (AsCompose f g x) where
  newtype Data (AsCompose f g x) a = D (Data (f (g x)) a)

instance HasStack (AsCompose f g x) where
  newtype Stack (AsCompose f g x) a = S (Stack (f (g x)) a)

instance F.HasFn (f (g x)) => F.HasFn (AsCompose f g x) where
  lambda t f = C $ F.lambda t (Path.make unC . f . Path.make C)
  C f <*> C x = C (f F.<*> x)
