{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import qualified AsCallcc
import qualified AsCbpv
import AsCps
import qualified AsPorcelain
import AsText
import qualified Callcc
import qualified Cbpv
import Common
import qualified Constant
import qualified Core
import qualified CostInliner
import CostInliner (CostInliner)
import qualified Cps
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Word
import HasCode
import HasConstants
import HasGlobals
import qualified Interpreter
import qualified Intrinsify
import MonoInliner (MonoInliner)
import qualified MonoInliner
import qualified Pure
import qualified SystemF as F
import TextShow

iterTerm = 20

iterCbpv = 20

iterCallcc = 20

iterCps = 20

program :: F.SystemF t => CodeRep t (F U64 :-> F U64 :-> F U64)
program = F.lam $ \x ->
  F.lam $ \y ->
    ( F.lam $ \z ->
        global Core.plus F.<*> z F.<*> y
    )
      F.<*> (global Core.plus F.<*> Pure.pure (constant (Constant.U64Constant 8)) F.<*> y)

phases ::
  F.Term a ->
  ( F.Term a,
    Cbpv.Code a,
    Cbpv.Code a,
    Cbpv.Code a,
    Callcc.Code a,
    Callcc.Code a,
    Cps.Data (U a),
    Cps.Data (U a)
  )
phases term =
  let optTerm = optimizeTerm term
      cbpv = Cbpv.build (AsCbpv.extract (F.interpret optTerm))
      intrinsified = Cbpv.build (Intrinsify.intrinsify cbpv)
      optIntrinsified = optimizeCbpv intrinsified
      catchThrow = Callcc.build (AsCallcc.extract (Cbpv.abstractCode optIntrinsified))
      optCatchThrow = optimizeCallcc catchThrow
      cps = Cps.build (toContinuationPassingStyle optCatchThrow)
      optCps = optimizeCps cps
   in (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps, optCps)

type OptF t = F.Simplifier (MonoInliner (CostInliner t))

optimizeTerm :: F.Term a -> F.Term a
optimizeTerm = loop iterTerm
  where
    step :: F.SystemF t => CodeRep (OptF t) a -> CodeRep t a
    step term =
      let simplified = F.simplify term
          monoInlined = MonoInliner.extract simplified
          inlined = CostInliner.extract monoInlined
       in inlined
    loop :: Int -> F.Term a -> F.Term a
    loop 0 term = term
    loop n term = loop (n - 1) (F.box (step (F.interpret term)))

optimizeCbpv :: Cbpv.Code a -> Cbpv.Code a
optimizeCbpv = loop iterCbpv
  where
    loop :: Int -> Cbpv.Code a -> Cbpv.Code a
    loop 0 term = term
    loop n term =
      loop (n - 1) ((costInline . monoInline . Cbpv.simplify) term)
    monoInline :: Cbpv.Code a -> Cbpv.Code a
    monoInline term =
      let x = MonoInliner.extract (Cbpv.abstractCode term)
       in Cbpv.build x
    costInline :: Cbpv.Code a -> Cbpv.Code a
    costInline term =
      let x = CostInliner.extract (Cbpv.abstractCode term)
       in Cbpv.build x

optimizeCallcc :: Callcc.Code a -> Callcc.Code a
optimizeCallcc = loop iterCallcc
  where
    loop :: Int -> Callcc.Code a -> Callcc.Code a
    loop 0 term = term
    loop n term =
      loop (n - 1) ((costInline . monoInline . Callcc.simplify) term)
    monoInline :: Callcc.Code a -> Callcc.Code a
    monoInline term =
      let x = MonoInliner.extract (Callcc.abstractCode term)
       in Callcc.build x
    costInline :: Callcc.Code a -> Callcc.Code a
    costInline term =
      let x = CostInliner.extract (Callcc.abstractCode term)
       in Callcc.build x

optimizeCps :: Cps.Data a -> Cps.Data a
optimizeCps = loop iterCps
  where
    loop :: Int -> Cps.Data a -> Cps.Data a
    loop 0 term = term
    loop n term =
      loop (n - 1) ((costInline . monoInline . Cps.simplify) term)
    monoInline :: Cps.Data a -> Cps.Data a
    monoInline term =
      let x = MonoInliner.extractData (Cps.abstract term)
       in Cps.build x
    costInline :: Cps.Data a -> Cps.Data a
    costInline term =
      let x = CostInliner.extractData (Cps.abstract term)
       in Cps.build x

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  T.putStrLn (AsText.extract program)

  let (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps, optCps) = phases (F.box program)

  putStrLn "\nOptimized Term:"
  T.putStrLn (AsText.extract (F.interpret optTerm))

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extract (Cbpv.abstractCode cbpv))

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extract (Cbpv.abstractCode intrinsified))

  putStrLn "\nOptimized Intrinsified:"
  T.putStrLn (AsText.extract (Cbpv.abstractCode optIntrinsified))

  putStrLn "\nCatch/Throw:"
  T.putStrLn (AsText.extract (Callcc.abstractCode catchThrow))

  putStrLn "\nOptimized Catch/Throw:"
  T.putStrLn (AsText.extract (Callcc.abstractCode optCatchThrow))

  putStrLn "\nCps:"
  T.putStrLn (AsText.extractData (Cps.abstract cps))

  putStrLn "\nOptimized Cps:"
  T.putStrLn (AsText.extractData (Cps.abstract optCps))

  putStrLn "\nPorcelain Output:"
  T.putStrLn (AsPorcelain.extract (Cps.abstract optCps))

  putStrLn "\nEvaluates to:"
  let cpsData = Interpreter.evaluate optCps

  let Interpreter.Thunk k = cpsData
  let Interpreter.Behaviour eff = k (t 4 `Interpreter.Apply` t 8 `Interpreter.Apply` (Interpreter.Returns $ \(Interpreter.I x) -> Interpreter.Behaviour $ printT x))
  eff

  return ()

t :: Word64 -> Interpreter.Value (U (F U64))
t x = Interpreter.Thunk $ \(Interpreter.Returns k) -> k (Interpreter.I x)
