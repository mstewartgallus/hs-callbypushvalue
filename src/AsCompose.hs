{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCompose ((:.:), extract, extractTerm, extractData, extractStack, Stack (..), Data (..), Code (..)) where

import Cbpv
import qualified Cps
import HasCall
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasTerm
import HasTerminal
import HasTuple
import NatTrans
import qualified SystemF as F

extract :: Code (AsCompose f g x) :~> Code (f (g x))
extract = NatTrans unC

extractTerm :: Term (AsCompose f g x) :~> Term (f (g x))
extractTerm = NatTrans unT

extractData :: Data (AsCompose f g x) :~> Data (f (g x))
extractData = NatTrans unD

extractStack :: Stack (AsCompose f g x) :~> Stack (f (g x))
extractStack = NatTrans unS

type (:.:) = AsCompose

infixr 0 :.:

newtype AsCompose f g x = AsCompose (f (g x))
  deriving
    ( HasCall,
      Cps.HasCall,
      F.HasConstants,
      F.HasLet,
      F.HasCall,
      F.HasTuple,
      F.HasFn,
      HasConstants,
      HasLet,
      HasFn,
      HasThunk,
      HasReturn,
      HasTuple,
      HasTerminal,
      Cps.HasLabel,
      Cps.HasThunk,
      Cps.HasReturn,
      Cps.HasFn
    )

instance HasCode (AsCompose f g x) where
  newtype Code (AsCompose f g x) a = C {unC :: Code (f (g x)) a}

instance HasTerm (AsCompose f g x) where
  newtype Term (AsCompose f g x) a = T {unT :: Term (f (g x)) a}

instance HasData (AsCompose f g x) where
  newtype Data (AsCompose f g x) a = D {unD :: Data (f (g x)) a}

instance HasStack (AsCompose f g x) where
  newtype Stack (AsCompose f g x) a = S {unS :: Stack (f (g x)) a}
