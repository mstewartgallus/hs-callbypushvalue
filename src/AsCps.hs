{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AsCps (toContinuationPassingStyle) where

import Basic
import qualified Callcc
import Common
import Const
import qualified Constant
import Core
import qualified Cps
import Explicit
import Global
import HasCode
import HasData
import qualified Pure
import Tuple

toContinuationPassingStyle :: (HasCode t, Cps.Cps t) => Callcc.Code a -> SetRep t (U a)
toContinuationPassingStyle code = case Callcc.abstractCode code of
  CodeCallcc t x -> Cps.thunk t x

data AsCps t

instance HasCode t => HasCode (AsCps t) where
  data AlgRep (AsCps t) a = CodeCallcc (SAlgebra a) (Cps.StackRep t a -> AlgRep t Void)

instance HasData t => HasData (AsCps t) where
  data SetRep (AsCps t) a = DataCallcc (SSet a) (SetRep t a)

instance (HasCode t, Cps.Cps t) => Basic (AsCps t) where
  global g@(Global t _) = CodeCallcc t $ \stack -> Cps.global g stack

instance (HasData t, Const t) => Const (AsCps t) where
  constant k = DataCallcc (Constant.typeOf k) $ constant k

instance (HasCode t, Cps.Cps t) => Pure.Pure (AsCps t) where
  pure (DataCallcc t x) = CodeCallcc (SF t) $ \k -> Cps.throw k x

instance (Cps.Cps t) => Explicit (AsCps t) where
  letBe (DataCallcc t x) f =
    let CodeCallcc b _ = f (DataCallcc t x)
     in CodeCallcc b $ \k ->
          Cps.throw
            ( Cps.letTo t $ \val ->
                case f (DataCallcc t val) of
                  CodeCallcc _ f' -> f' k
            )
            x

  letTo (CodeCallcc (SF t) x) f =
    let CodeCallcc b _ = f (DataCallcc t undefined)
     in CodeCallcc b $ \k ->
          x
            ( Cps.letTo t $ \val ->
                case f (DataCallcc t val) of
                  CodeCallcc _ f' -> f' k
            )

  lambda t f =
    let CodeCallcc bt _ = f (DataCallcc t undefined)
     in CodeCallcc (t `SFn` bt) $ \k -> Cps.lambda k $ \x k ->
          let CodeCallcc _ body = f (DataCallcc t x)
           in body k
  apply (CodeCallcc (_ `SFn` b) f) (DataCallcc _ x) = CodeCallcc b $ \k -> f (Cps.apply x k)

instance (HasCode t, Cps.Cps t) => Tuple (AsCps t)

instance (HasCode t, Cps.Cps t) => Callcc.Callcc (AsCps t) where
  data StackRep (AsCps t) a = SB (SAlgebra a) (Cps.StackRep t a)

  thunk t f = DataCallcc (SU t) $ Cps.thunk t $ \k ->
    case f (SB t k) of
      CodeCallcc _ y -> y Cps.nil

  force (DataCallcc _ thunk) (SB _ stack) = CodeCallcc SVoid $ \_ ->
    Cps.force thunk stack

  catch t f = CodeCallcc t $ \k ->
    Cps.force
      ( Cps.thunk t $ \k' ->
          case f (SB t k') of
            CodeCallcc _ y -> y Cps.nil
      )
      k
  throw (SB _ x) (CodeCallcc _ f) = CodeCallcc SVoid $ \_ -> f x
