{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import qualified AsCbpv
import qualified AsCps
import qualified AsIntrinsified
import qualified AsMemoized
import qualified AsPorcelain
import AsText
import Cbpv (Cbpv)
import qualified Cbpv
import Cbpv (HasCall (..), HasReturn (..), HasThunk (..))
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

iterCps = 20

program :: SystemF t => Code t (F U64 :-> F U64 :-> F U64)
program = F.lam $ \x ->
  F.lam $ \y ->
    ( F.lam $ \z ->
        call Core.plus F.<*> z F.<*> y
    )
      F.<*> (call Core.plus F.<*> returns (constant (Constant.U64Constant 8)) F.<*> y)

phases ::
  Program SystemF a ->
  ( Program SystemF a,
    Value Cbpv (U a),
    Value Cbpv (U a),
    Value Cbpv (U a),
    Value Cps (U a),
    Value Cps (U a)
  )
phases term =
  let optTerm = optimizeTerm term
      cbpv = cbpvValue (thunk (AsCbpv.extract (Program.interpret optTerm)))
      intrinsified = cbpvValue (AsIntrinsified.extract (Value.interpret cbpv))
      optIntrinsified = optimizeCbpv intrinsified
      cps = cpsValue (AsCps.extract (Value.interpret optIntrinsified))
      optCps = optimizeCps cps
   in (optTerm, cbpv, intrinsified, optIntrinsified, cps, optCps)

cbpvValue :: (forall t. Cbpv t => Data t a) -> Value Cbpv a
cbpvValue = Value

cpsValue :: (forall t. Cps t => Data t a) -> Value Cps a
cpsValue = Value

type OptF t = SystemFSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeTerm :: Program SystemF a -> Program SystemF a
optimizeTerm = loop iterTerm
  where
    step :: SystemF t => Code (OptF t) a -> Code t a
    step term =
      let simplified = SystemFSimplifier.extract term
          monoInlined = MonoInliner.extract simplified
          inlined = CostInliner.extract monoInlined
       in inlined
    loop :: Int -> Program SystemF a -> Program SystemF a
    loop 0 term = term
    loop n term = loop (n - 1) (AsMemoized.extract (step (Program.interpret term)))

type OptC t = CbpvSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCbpv :: Value Cbpv a -> Value Cbpv a
optimizeCbpv = loop iterCbpv
  where
    step :: Cbpv t => Data (OptC t) a -> Data t a
    step term =
      let simplified = CbpvSimplifier.extract term
          monoInlined = MonoInliner.extractData simplified
          inlined = CostInliner.extractData monoInlined
       in inlined
    loop :: Int -> Value Cbpv a -> Value Cbpv a
    loop 0 term = term
    loop n term = loop (n - 1) (Value (step (Value.interpret term)))

type OptCps t = CpsSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCps :: Value Cps a -> Value Cps a
optimizeCps = loop iterCps
  where
    step :: Cps t => Data (OptCps t) a -> Data t a
    step term =
      let simplified = CpsSimplifier.extract term
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

  let (optTerm, cbpv, intrinsified, optIntrinsified, cps, optCps) = phases (Program program)

  putStrLn "\nOptimized Term:"
  T.putStrLn (AsText.extract (Program.interpret optTerm))

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extractData (Value.interpret cbpv))

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extractData (Value.interpret intrinsified))

  putStrLn "\nOptimized Intrinsified:"
  T.putStrLn (AsText.extractData (Value.interpret optIntrinsified))

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
