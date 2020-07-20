{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Duplicate (Factory, extract) where

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

extract :: Code Factory a -> Program SystemF a
extract (FacC x) =
  let GenC y = Unique.withStream x
   in Program (y LabelMap.empty)

data Factory

data Generic (k :: * -> Constraint)

instance HasCode (Generic k) where
  newtype Code (Generic k) a = GenC (forall t. k t => LabelMap (Code t) -> Code t a)

instance HasData (Generic k) where
  newtype Data (Generic k) a = GenD (forall t. k t => LabelMap (Code t) -> Data t a)

instance HasCode Factory where
  newtype Code Factory a = FacC (forall x. Unique.Stream x -> Code (Generic SystemF) a)

instance HasData Factory where
  newtype Data Factory a = FacD (forall x. Unique.Stream x -> Data (Generic SystemF) a)

instance HasGlobals Factory where
  global g = FacC $ \_ ->
    GenC $
      let g' = global g
       in \_ -> g'

instance HasConstants Factory where
  constant k = FacD $ \_ ->
    GenD $
      let k' = constant k
       in \_ -> k'
  unit = FacD $ \_ ->
    GenD $
      let u = unit
       in \_ -> u

instance HasReturn Factory where
  returns (FacD x) = FacC $ \xs ->
    let GenD x' = x xs
     in GenC $ \env -> returns (x' env)

instance SystemF.SystemF Factory where
  -- --   pair (GenC x) (GenC y) = GenC $ \env -> SystemF.pair (x env) (y env)

  letBe (FacC x) f = FacC $ \(Unique.Stream newId xs ys) ->
    let GenC x' = x xs
        binder = Label undefined newId
        FacC y = f $ FacC $ \_ -> GenC $ \env -> case LabelMap.lookup binder env of
          Just x -> x
        GenC y' = y ys
     in GenC $ \env ->
          SystemF.letBe (x' env) $ \val -> y' (LabelMap.insert binder val env)

  lambda t f = FacC $ \(Unique.Stream newId _ ys) ->
    let binder = Label t newId
        FacC y =
          f $ FacC $ \_ -> GenC $ \env -> case LabelMap.lookup binder env of
            Just x -> x
        GenC y' = y ys
     in GenC $ \env ->
          SystemF.lambda t $ \val -> y' (LabelMap.insert binder val env)

  FacC f <*> FacC x = FacC $ \(Unique.Stream _ fs xs) ->
    let GenC f' = f fs
        GenC x' = x xs
     in GenC $ \env -> f' env SystemF.<*> x' env
