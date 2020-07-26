{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module AsMemoized (AsMemoized, extract) where

import Box
import Cbpv (HasCall (..), HasReturn (..))
import Common
import qualified Cps
import qualified Data.Text as T
import GHC.Exts (Constraint)
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import SystemF (HasFn, HasTuple, SystemF)
import qualified SystemF
import TextShow
import qualified Unique
import Prelude hiding ((<*>))

extract :: Code (AsMemoized k) a -> Code (Box k) a
extract (C x) = mkProgram (Unique.withStream x LabelMap.empty)

data AsMemoized (k :: * -> Constraint)

instance HasCode (AsMemoized k) where
  newtype Code (AsMemoized k) a = C (forall x. Unique.Stream x -> (forall t. k t => LabelMap (Code t) -> Code t a))

instance HasData (AsMemoized k) where
  newtype Data (AsMemoized k) a = D (forall x. Unique.Stream x -> (forall t. k t => LabelMap (Code t) -> Data t a))

instance HasCall (AsMemoized SystemF) where
  call g = C $ \_ ->
    let g' = call g
     in \_ -> g'

instance HasConstants (AsMemoized SystemF) where
  constant k = D $ \_ ->
    let k' = constant k
     in \_ -> k'

instance HasReturn (AsMemoized SystemF) where
  returns (D x) = C $ \xs ->
    let x' = x xs
     in \env -> returns (x' env)

instance SystemF.HasLet (AsMemoized SystemF) where
  letBe (C x) f = C $ \(Unique.Stream newId xs ys) ->
    let x' = x xs
        binder = Label undefined newId
        C y = f $ C $ \_ -> \env -> case LabelMap.lookup binder env of
          Just x -> x
        y' = y ys
     in \env ->
          SystemF.letBe (x' env) $ \val -> y' (LabelMap.insert binder val env)

instance HasTuple (AsMemoized SystemF)

instance HasFn (AsMemoized SystemF) where
  lambda t f = C $ \(Unique.Stream newId _ ys) ->
    let binder = Label t newId
        C y =
          f $ C $ \_ -> \env -> case LabelMap.lookup binder env of
            Just x -> x
        y' = y ys
     in \env ->
          SystemF.lambda t $ \val -> y' (LabelMap.insert binder val env)

  C f <*> C x = C $ \(Unique.Stream _ fs xs) ->
    let f' = f fs
        x' = x xs
     in \env -> f' env SystemF.<*> x' env
