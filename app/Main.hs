{-# LANGUAGE TypeOperators #-}

module Main where

import AsCbpv (AsCbpv)
import qualified AsCbpv
import qualified AsCompose
import AsCompose ((:.:))
import qualified AsCps
import AsCps (AsCps)
import qualified AsDup
import AsDup (AsDup)
import AsIntrinsified (AsIntrinsified)
import qualified AsIntrinsified
import qualified AsPorcelain
import AsText
import Cbpv (Cbpv)
import Cbpv (HasThunk (..))
import qualified CbpvSimplifyApply
import qualified CbpvSimplifyForce
import qualified CbpvSimplifyReturn
import Common
import qualified Constant
import Control.Category
import qualified Core
import qualified CostInliner
import CostInliner (CostInliner)
import Cps (Cps)
import qualified CpsSimplifyApply
import qualified CpsSimplifyForce
import qualified CpsSimplifyLet
import qualified Data.Text.IO as T
import Data.Word
import HasCall
import HasCode
import HasData
import qualified Interpreter
import MonoInliner (MonoInliner)
import qualified MonoInliner
import NatTrans
import PairF
import SystemF (SystemF)
import qualified SystemF as F
import qualified SystemFSimplifier
import TextShow
import Prelude hiding ((.), id)

iterTerm :: Int
iterTerm = 20

iterCbpv :: Int
iterCbpv = 20

iterCps :: Int
iterCps = 20

program :: SystemF t => Code t (F U64 :-> F U64 :-> F U64)
program = F.lam $ \_ ->
  F.lam $ \y ->
    ( F.lam $ \z ->
        call Core.plus F.<*> z F.<*> y
    )
      F.<*> (call Core.plus F.<*> F.constant (Constant.U64Constant 8) F.<*> y)

main :: IO ()
main = do
  copy <- dupLog program
  optTerm <- optimizeTerm copy
  cbpv <- cbpvTerm optTerm
  intrinsified <- intrinsify cbpv
  optCbpv <- optimizeCbpv intrinsified
  cps <- cpsTerm (Cbpv.thunk optCbpv)
  optCps <- optimizeCps cps

  let PairF porcelain interpreter = AsDup.extractData # optCps

  putStrLn "\nPorcelain Output:"
  T.putStrLn (AsPorcelain.extract porcelain)

  putStrLn "\nEvaluates to:"
  let cpsData = Interpreter.evaluate interpreter

  let Interpreter.Thunk k = cpsData
  let Interpreter.Behaviour eff = k (t 4 `Interpreter.Apply` t 8 `Interpreter.Apply` (Interpreter.Returns $ \(Interpreter.I x) -> Interpreter.Behaviour $ printT x))
  eff

  return ()

dupLog :: SystemF t => Code (AsDup AsText t) a -> IO (Code t a)
dupLog term = do
  let PairF text copy = AsDup.extract # term

  putStrLn "Lambda Calculus:"
  T.putStrLn (AsText.extract text)

  return copy

cbpvTerm :: Cbpv t => Code ((AsCbpv :.: AsDup AsText) t) a -> IO (Code t a)
cbpvTerm term = do
  let PairF text copy = (AsDup.extract . AsCbpv.extract . AsCompose.extract) # term

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extract text)

  return copy

intrinsify :: Cbpv t => Code ((AsIntrinsified :.: AsDup AsText) t) a -> IO (Code t a)
intrinsify term = do
  let PairF text copy = (AsDup.extract . AsIntrinsified.extract . AsCompose.extract) # term

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extract text)

  return copy

cpsTerm :: Cps t => Data ((AsCps :.: AsDup AsText) t) a -> IO (Data t a)
cpsTerm term = do
  let PairF text copy = (AsDup.extractData . AsCps.extract . AsCompose.extractData) # term

  putStrLn "\nContinuation Passing Style:"
  T.putStrLn (AsText.extractData text)

  return copy

type OptF = SystemFSimplifier.Simplifier :.: MonoInliner :.: CostInliner

-- fixme... loop
optimizeTerm :: SystemF t => Code (OptF (AsDup AsText t)) a -> IO (Code t a)
optimizeTerm input =
  let step :: SystemF t => Code (OptF t) :~> Code t
      step =
        CostInliner.extract
          . MonoInliner.extract
          . AsCompose.extract
          . SystemFSimplifier.extract
          . AsCompose.extract
   in do
        let PairF text copy = (AsDup.extract . step) # input
        putStrLn "\nOptimized Term:"
        T.putStrLn (AsText.extract text)

        return copy

type OptC = CbpvSimplifyForce.Simplifier :.: CbpvSimplifyApply.Simplifier :.: CbpvSimplifyReturn.Simplifier :.: MonoInliner :.: CostInliner

-- fixme... loop
optimizeCbpv :: Cbpv t => Code (OptC (AsDup AsText t)) a -> IO (Code t a)
optimizeCbpv input =
  let step :: Cbpv t => Code (OptC t) :~> Code t
      step =
        CostInliner.extract
          . MonoInliner.extract
          . AsCompose.extract
          . CbpvSimplifyReturn.extract
          . AsCompose.extract
          . CbpvSimplifyApply.extract
          . AsCompose.extract
          . CbpvSimplifyForce.extract
          . AsCompose.extract
   in do
        let PairF text copy = (AsDup.extract . step) # input
        putStrLn "\nOptimized Call By Push Value:"
        T.putStrLn (AsText.extract text)

        return copy

type OptCps = CpsSimplifyLet.Simplifier :.: CpsSimplifyForce.Simplifier :.: CpsSimplifyApply.Simplifier :.: MonoInliner :.: CostInliner

optimizeCps :: Cps t => Data (OptCps (AsDup AsText t)) a -> IO (Data t a)
optimizeCps input =
  let step :: Cps t => Data (OptCps t) :~> Data t
      step =
        CostInliner.extractData
          . MonoInliner.extractData
          . AsCompose.extractData
          . CpsSimplifyApply.extract
          . AsCompose.extractData
          . CpsSimplifyForce.extract
          . AsCompose.extractData
          . CpsSimplifyLet.extract
          . AsCompose.extractData
   in do
        let PairF text copy = (AsDup.extractData . step) # input
        putStrLn "\nOptimized Continuation Passing Style:"
        T.putStrLn (AsText.extractData text)

        return copy

t :: Word64 -> Interpreter.Value (U (F U64))
t x = Interpreter.Thunk $ \(Interpreter.Returns k) -> k (Interpreter.I x)
