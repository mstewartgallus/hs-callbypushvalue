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

phases ::
  Code (Box SystemF) a ->
  ( Code (Box SystemF) a,
    Data (Box Cbpv) (U a),
    Data (Box Cbpv) (U a),
    Data (Box Cbpv) (U a),
    Data (Box Cps) (U a),
    Data (Box Cps) (U a)
  )
phases term =
  let optTerm = optimizeTerm term
      cbpv = cbpvValue (thunk (AsCbpv.extract (Box.interpret optTerm)))
      intrinsified = cbpvValue (AsIntrinsified.extract (Box.interpretValue cbpv))
      optIntrinsified = optimizeCbpv intrinsified
      cps = cpsValue (AsCps.extract (Box.interpretValue optIntrinsified))
      optCps = optimizeCps cps
   in (optTerm, cbpv, intrinsified, optIntrinsified, cps, optCps)

cbpvValue :: (forall t. Cbpv t => Data t a) -> Data (Box Cbpv) a
cbpvValue = mkValue

cpsValue :: (forall t. Cps t => Data t a) -> Data (Box Cps) a
cpsValue = mkValue

type OptF t = SystemFSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeTerm :: Code (Box SystemF) a -> Code (Box SystemF) a
optimizeTerm = loop iterTerm
  where
    step :: SystemF t => Code (OptF t) a -> Code t a
    step term =
      let simplified = SystemFSimplifier.extract term
          monoInlined = MonoInliner.extract simplified
          inlined = CostInliner.extract monoInlined
       in inlined
    loop :: Int -> Code (Box SystemF) a -> Code (Box SystemF) a
    loop 0 term = term
    loop n term = loop (n - 1) (AsMemoized.extract (step (Box.interpret term)))

type OptC t = CbpvSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCbpv :: Data (Box Cbpv) a -> Data (Box Cbpv) a
optimizeCbpv = loop iterCbpv
  where
    step :: Cbpv t => Data (OptC t) a -> Data t a
    step term =
      let simplified = CbpvSimplifier.extract term
          monoInlined = MonoInliner.extractData simplified
          inlined = CostInliner.extractData monoInlined
       in inlined
    loop :: Int -> Data (Box Cbpv) a -> Data (Box Cbpv) a
    loop 0 term = term
    loop n term = loop (n - 1) (mkValue (step (Box.interpretValue term)))

type OptCps t = CpsSimplifier.Simplifier (MonoInliner (CostInliner t))

optimizeCps :: Data (Box Cps) a -> Data (Box Cps) a
optimizeCps = loop iterCps
  where
    step :: Cps t => Data (OptCps t) a -> Data t a
    step term =
      let simplified = CpsSimplifier.extract term
          monoInlined = MonoInliner.extractData simplified
          inlined = CostInliner.extractData monoInlined
       in inlined
    loop :: Int -> Data (Box Cps) a -> Data (Box Cps) a
    loop 0 term = term
    loop n term = loop (n - 1) (mkValue (step (Box.interpretValue term)))

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  T.putStrLn (AsText.extract program)

  let (optTerm, cbpv, intrinsified, optIntrinsified, cps, optCps) = phases (mkProgram program)

  putStrLn "\nOptimized Term:"
  T.putStrLn (AsText.extract (Box.interpret optTerm))

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extractData (Box.interpretValue cbpv))

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extractData (Box.interpretValue intrinsified))

  putStrLn "\nOptimized Intrinsified:"
  T.putStrLn (AsText.extractData (Box.interpretValue optIntrinsified))

  putStrLn "\nCps:"
  T.putStrLn (AsText.extractData (Box.interpretValue cps))

  putStrLn "\nOptimized Cps:"
  T.putStrLn (AsText.extractData (Box.interpretValue optCps))

  putStrLn "\nPorcelain Output:"
  T.putStrLn (AsPorcelain.extract (Box.interpretValue optCps))

  putStrLn "\nEvaluates to:"
  let cpsData = Interpreter.evaluate (Box.interpretValue optCps)

  let Interpreter.Thunk k = cpsData
  let Interpreter.Behaviour eff = k (t 4 `Interpreter.Apply` t 8 `Interpreter.Apply` (Interpreter.Returns $ \(Interpreter.I x) -> Interpreter.Behaviour $ printT x))
  eff

  return ()

t :: Word64 -> Interpreter.Value (U (F U64))
t x = Interpreter.Thunk $ \(Interpreter.Returns k) -> k (Interpreter.I x)
