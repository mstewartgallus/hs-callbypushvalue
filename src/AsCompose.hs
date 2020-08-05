{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCompose ((:.:), extract, extractData, extractStack) where

import Cbpv
import Common
import qualified Cps
import Global
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTuple
import NatTrans
import SystemF (SystemF)
import qualified SystemF as F
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
      F.HasFn,
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
  newtype Code (AsCompose f g x) a = C (Code (f (g x)) a)

instance HasData (AsCompose f g x) where
  newtype Data (AsCompose f g x) a = D (Data (f (g x)) a)

instance HasStack (AsCompose f g x) where
  newtype Stack (AsCompose f g x) a = S (Stack (f (g x)) a)
