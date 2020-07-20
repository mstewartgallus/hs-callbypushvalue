{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Duplicate (Factory, Generic, extract, copy) where

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
import SystemF (SystemF)
import qualified SystemF
import TextShow
import qualified Unique
import Prelude hiding ((<*>))

extract :: Code Factory a -> Code Generic a
extract (FacC x) = GenC (Unique.withStream x)

data Generic

copy :: SystemF t => Code Generic a -> Code t a
copy (GenC x) = x LabelMap.empty

instance HasCode Generic where
  newtype Code Generic a = GenC (forall t. SystemF t => LabelMap (Code t) -> Code t a)

data Factory

instance HasCode Factory where
  newtype Code Factory a = FacC (forall x. Unique.Stream x -> (forall t. SystemF t => LabelMap (Code t) -> Code t a))

instance HasData Factory where
  newtype Data Factory a = FacD (forall x. Unique.Stream x -> (forall t. SystemF t => LabelMap (Code t) -> Data t a))

instance HasGlobals Factory where
  global g = FacC $ \_ ->
    let g' = global g
     in \_ -> g'

instance HasConstants Factory where
  constant k = FacD $ \_ ->
    let k' = constant k
     in \_ -> k'
  unit = FacD $ \_ ->
    let u = unit
     in \_ -> u

instance HasReturn Factory where
  returns (FacD x) = FacC $ \xs ->
    let x' = x xs
     in \env -> returns (x' env)

instance SystemF.SystemF Factory where
  -- --   pair (GenC x) (GenC y) = GenC $ \env -> SystemF.pair (x env) (y env)

  letBe (FacC x) f = FacC $ \(Unique.Stream newId xs ys) ->
    let x' = x xs
        binder = Label undefined newId
        FacC y =
          f
            ( FacC $ \_ -> \env -> case LabelMap.lookup binder env of
                Just x -> x
            )
        y' = y ys
     in \env ->
          SystemF.letBe (x' env) $ \val -> y' (LabelMap.insert binder val env)

  lambda t f = FacC $ \(Unique.Stream newId _ ys) ->
    let binder = Label t newId
        FacC y =
          f
            ( FacC $ \_ -> \env -> case LabelMap.lookup binder env of
                Just x -> x
            )
        y' = y ys
     in \env ->
          SystemF.lambda t $ \val -> y' (LabelMap.insert binder val env)

  FacC f <*> FacC x = FacC $ \(Unique.Stream _ fs xs) ->
    let f' = f fs
        x' = x xs
     in \env -> f' env SystemF.<*> x' env
