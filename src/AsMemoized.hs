{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module AsMemoized (AsMemoized, extract) where

import qualified Callcc
import Cbpv
import Common
import qualified Cps
import qualified Data.Text as T
import GHC.Exts (Constraint)
import Global
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasLet
import HasLetLabel
import HasLetTo
import HasReturn
import HasStack
import qualified HasThunk
import HasTuple
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import Name
import Program (Program (..))
import SystemF (SystemF)
import qualified SystemF
import TextShow
import qualified Unique
import Prelude hiding ((<*>))

extract :: Code (AsMemoized k) a -> Program k a
extract (C x) = Program (Unique.withStream x LabelMap.empty)

data AsMemoized (k :: * -> Constraint)

instance HasCode (AsMemoized k) where
  newtype Code (AsMemoized k) a = C (forall x. Unique.Stream x -> (forall t. k t => LabelMap (Code t) -> Code t a))

instance HasData (AsMemoized k) where
  newtype Data (AsMemoized k) a = D (forall x. Unique.Stream x -> (forall t. k t => LabelMap (Code t) -> Data t a))

instance HasGlobals (AsMemoized SystemF) where
  global g = C $ \_ ->
    let g' = global g
     in \_ -> g'

instance HasConstants (AsMemoized SystemF) where
  constant k = D $ \_ ->
    let k' = constant k
     in \_ -> k'
  unit = D $ \_ ->
    let u = unit
     in \_ -> u

instance HasReturn (AsMemoized SystemF) where
  returns (D x) = C $ \xs ->
    let x' = x xs
     in \env -> returns (x' env)

instance SystemF (AsMemoized SystemF) where
  -- --   pair (  x) (  y) =  \env -> SystemF.pair (x env) (y env)

  letBe (C x) f = C $ \(Unique.Stream newId xs ys) ->
    let x' = x xs
        binder = Label undefined newId
        C y = f $ C $ \_ -> \env -> case LabelMap.lookup binder env of
          Just x -> x
        y' = y ys
     in \env ->
          SystemF.letBe (x' env) $ \val -> y' (LabelMap.insert binder val env)

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
