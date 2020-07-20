{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import qualified AsCallcc
import qualified AsCbpv
import AsCps
import qualified AsIntrinsified
import qualified AsMemoized
import qualified AsPorcelain
import AsText
import qualified Callcc
import Callcc (Callcc)
import qualified CallccSimplifier
import Cbpv (Cbpv)
import qualified Cbpv
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
import HasCode
import HasConstants
import HasData
import HasGlobals
import HasReturn
import qualified Interpreter
import MonoInliner (MonoInliner)
import qualified MonoInliner
import Program (Program (..))
import qualified Program
import SystemF (SystemF)
import qualified SystemF as F
import qualified SystemFSimplifier
import TextShow
import Value (Value (..))
import qualified Value

iterTerm = 20

iterCbpv = 20

iterCallcc = 20

iterCps = 20

program :: SystemF t => Code t (F U64 :-> F U64 :-> F U64)
program = F.lam $ \x ->
  F.lam $ \y ->
    ( F.lam $ \z ->
        global Core.plus F.<*> z F.<*> y
    )
      F.<*> (global Core.plus F.<*> returns (constant (Constant.U64Constant 8)) F.<*> y)

phases ::
  Program SystemF a ->
  ( Program SystemF a,
    Program Cbpv a,
    Program Cbpv a,
    Program Cbpv a,
    Program Callcc a,
    Program Callcc a,
    Value Cps (U a),
    Value Cps (U a)
  )
phases term =
  let optTerm = optimizeTerm term
      cbpv = cbpvProgram (AsCbpv.extract (Program.interpret optTerm))
      intrinsified = cbpvProgram (AsIntrinsified.extract (Program.interpret cbpv))
      optIntrinsified = optimizeCbpv intrinsified
      catchThrow = callccProgram (AsCallcc.extract (Program.interpret optIntrinsified))
      optCatchThrow = optimizeCallcc catchThrow
      cps = cpsValue (toContinuationPassingStyle (Program.interpret optCatchThrow))
      optCps = optimizeCps cps
   in (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps, optCps)

cbpvProgram :: (forall t. Cbpv t => Code t a) -> Program Cbpv a
cbpvProgram = Program

callccProgram :: (forall t. Callcc t => Code t a) -> Program Callcc a
callccProgram = Program

cpsValue :: (forall t. Cps t => Data t a) -> Value Cps a
cpsValue = Value

type OptF t = SystemFSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeTerm :: Program SystemF a -> Program SystemF a
optimizeTerm = loop iterTerm
  where
    step :: SystemF t => Code (OptF t) a -> Code t a
    step term =
      let simplified = SystemFSimplifier.simplify term
          monoInlined = MonoInliner.extract simplified
          inlined = CostInliner.extract monoInlined
       in inlined
    loop :: Int -> Program SystemF a -> Program SystemF a
    loop 0 term = term
    loop n term = loop (n - 1) (AsMemoized.extract (step (Program.interpret term)))

type OptC t = CbpvSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCbpv :: Program Cbpv a -> Program Cbpv a
optimizeCbpv = loop iterCbpv
  where
    step :: Cbpv t => Code (OptC t) a -> Code t a
    step term =
      let simplified = CbpvSimplifier.simplifyExtract term
          monoInlined = MonoInliner.extract simplified
          inlined = CostInliner.extract monoInlined
       in inlined
    loop :: Int -> Program Cbpv a -> Program Cbpv a
    loop 0 term = term
    loop n term = loop (n - 1) (Program (step (Program.interpret term)))

type OptCallcc t = CallccSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCallcc :: Program Callcc a -> Program Callcc a
optimizeCallcc = loop iterCallcc
  where
    step :: Callcc t => Code (OptCallcc t) a -> Code t a
    step term =
      let simplified = CallccSimplifier.simplifyExtract term
          monoInlined = MonoInliner.extract simplified
          inlined = CostInliner.extract monoInlined
       in inlined
    loop :: Int -> Program Callcc a -> Program Callcc a
    loop 0 term = term
    loop n term = loop (n - 1) (Program (step (Program.interpret term)))

type OptCps t = CpsSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCps :: Value Cps a -> Value Cps a
optimizeCps = loop iterCps
  where
    step :: Cps t => Data (OptCps t) a -> Data t a
    step term =
      let simplified = CpsSimplifier.simplifyExtract term
          monoInlined = MonoInliner.extractData simplified
          inlined = CostInliner.extractData monoInlined
       in inlined
    loop :: Int -> Value Cps a -> Value Cps a
    loop 0 term = term
    loop n term = loop (n - 1) (Value (step (Value.interpret term)))

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  T.putStrLn (AsText.extract program)

  let (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps, optCps) = phases (Program program)

  putStrLn "\nOptimized Term:"
  T.putStrLn (AsText.extract (Program.interpret optTerm))

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extract (Program.interpret cbpv))

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extract (Program.interpret intrinsified))

  putStrLn "\nOptimized Intrinsified:"
  T.putStrLn (AsText.extract (Program.interpret optIntrinsified))

  putStrLn "\nCatch/Throw:"
  T.putStrLn (AsText.extract (Program.interpret catchThrow))

  putStrLn "\nOptimized Catch/Throw:"
  T.putStrLn (AsText.extract (Program.interpret optCatchThrow))

  putStrLn "\nCps:"
  T.putStrLn (AsText.extractData (Value.interpret cps))

  putStrLn "\nOptimized Cps:"
  T.putStrLn (AsText.extractData (Value.interpret optCps))

  putStrLn "\nPorcelain Output:"
  T.putStrLn (AsPorcelain.extract (Value.interpret optCps))

  putStrLn "\nEvaluates to:"
  let cpsData = Interpreter.evaluate (Value.interpret optCps)

  let Interpreter.Thunk k = cpsData
  let Interpreter.Behaviour eff = k (t 4 `Interpreter.Apply` t 8 `Interpreter.Apply` (Interpreter.Returns $ \(Interpreter.I x) -> Interpreter.Behaviour $ printT x))
  eff

  return ()

t :: Word64 -> Interpreter.Value (U (F U64))
t x = Interpreter.Thunk $ \(Interpreter.Returns k) -> k (Interpreter.I x)
