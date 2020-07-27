{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import AsCbpv (AsCbpv)
import qualified AsCbpv
import qualified AsCps
import AsCps (AsCps)
import qualified AsDup
import AsDup (AsDup)
import AsIntrinsified (AsIntrinsified)
import qualified AsIntrinsified
import qualified AsMemoized
import qualified AsPorcelain
import AsText
import Box (Box, mkProgram, mkValue)
import qualified Box
import Cbpv (Cbpv)
import qualified Cbpv
import Cbpv (HasThunk (..))
import qualified CbpvSimplifier
import Common
import qualified Constant
import qualified Core
import qualified CostInliner
import CostInliner (CostInliner)
import qualified Cps
import Cps (Cps)
import qualified CpsSimplifier
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Word
import HasCall
import HasCode
import HasData
import qualified Interpreter
import MonoInliner (MonoInliner)
import qualified MonoInliner
import SystemF (SystemF)
import qualified SystemF as F
import qualified SystemFSimplifier
import TextShow

iterTerm = 20

iterCbpv = 20

iterCps = 20

program :: SystemF t => Code t (F U64 :-> F U64 :-> F U64)
program = F.lam $ \x ->
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

  let (porcelain, interpreter) = AsDup.extractData optCps

  putStrLn "\nPorcelain Output:"
  T.putStrLn (AsPorcelain.extract porcelain)

  putStrLn "\nEvaluates to:"
  let cpsData = Interpreter.evaluate interpreter

  let Interpreter.Thunk k = cpsData
  let Interpreter.Behaviour eff = k (t 4 `Interpreter.Apply` t 8 `Interpreter.Apply` (Interpreter.Returns $ \(Interpreter.I x) -> Interpreter.Behaviour $ printT x))
  eff

  return ()

cbpvValue :: (forall t. Cbpv t => Data t a) -> Data (Box Cbpv) a
cbpvValue = mkValue

cpsValue :: (forall t. Cps t => Data t a) -> Data (Box Cps) a
cpsValue = mkValue

dupLog :: SystemF t => Code (AsDup AsText t) a -> IO (Code t a)
dupLog term = do
  let (text, copy) = AsDup.extract term

  putStrLn "Lambda Calculus:"
  T.putStrLn (AsText.extract text)

  return copy

cbpvTerm :: Cbpv t => Code (AsCbpv (AsDup AsText t)) a -> IO (Code t a)
cbpvTerm term = do
  let (text, copy) = AsDup.extract (AsCbpv.extract term)

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extract text)

  return copy

intrinsify :: Cbpv t => Code (AsIntrinsified (AsDup AsText t)) a -> IO (Code t a)
intrinsify term = do
  let (text, copy) = AsDup.extract (AsIntrinsified.extract term)

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extract text)

  return copy

cpsTerm :: Cps t => Data (AsCps (AsDup AsText t)) a -> IO (Data t a)
cpsTerm term = do
  let (text, copy) = AsDup.extractData (AsCps.extract term)

  putStrLn "\nContinuation Passing Style:"
  T.putStrLn (AsText.extractData text)

  return copy

type OptF t = SystemFSimplifier.Simplifier (MonoInliner (CostInliner t))

-- fixme... loop
optimizeTerm :: SystemF t => Code (OptF (AsDup AsText t)) a -> IO (Code t a)
optimizeTerm input =
  let step :: SystemF t => Code (OptF t) a -> Code t a
      step term =
        let simplified = SystemFSimplifier.extract term
            monoInlined = MonoInliner.extract simplified
            inlined = CostInliner.extract monoInlined
         in inlined
   in do
        let (text, copy) = AsDup.extract (step input)
        putStrLn "\nOptimized Term:"
        T.putStrLn (AsText.extract text)

        return copy

-- loop :: Int -> Code (Box SystemF) a -> Code (Box SystemF) a
-- loop 0 term = term
-- loop n term = loop (n - 1) (mkProgram (step (Box.interpret term)))

type OptC t = CbpvSimplifier.Simplifier (MonoInliner (CostInliner t))

-- fixme... loop
optimizeCbpv :: Cbpv t => Code (OptC (AsDup AsText t)) a -> IO (Code t a)
optimizeCbpv input =
  let step :: Cbpv t => Code (OptC t) a -> Code t a
      step term =
        let simplified = CbpvSimplifier.extract term
            monoInlined = MonoInliner.extract simplified
            inlined = CostInliner.extract monoInlined
         in inlined
   in do
        let (text, copy) = AsDup.extract (step input)
        putStrLn "\nOptimized Call By Push Value:"
        T.putStrLn (AsText.extract text)

        return copy

-- loop :: Int -> Data (Box Cbpv) a -> Data (Box Cbpv) a
-- loop 0 term = term
-- loop n term = loop (n - 1) (mkValue (step (Box.interpretValue term)))

type OptCps t = CpsSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCps :: Cps t => Data (OptCps (AsDup AsText t)) a -> IO (Data t a)
optimizeCps input =
  let step :: Cps t => Data (OptCps t) a -> Data t a
      step term =
        let simplified = CpsSimplifier.extract term
            monoInlined = MonoInliner.extractData simplified
            inlined = CostInliner.extractData monoInlined
         in inlined
   in do
        let (text, copy) = AsDup.extractData (step input)
        putStrLn "\nOptimized Continuation Passing Style:"
        T.putStrLn (AsText.extractData text)

        return copy

-- loop :: Int -> Data (Box Cps) a -> Data (Box Cps) a
-- loop 0 term = term
-- loop n term = loop (n - 1) (mkValue (step (Box.interpretValue term)))

t :: Word64 -> Interpreter.Value (U (F U64))
t x = Interpreter.Thunk $ \(Interpreter.Returns k) -> k (Interpreter.I x)
