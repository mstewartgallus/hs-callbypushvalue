{-# LANGUAGE GADTs #-}

module Main where

import qualified Callcc
import qualified Cbpv
import Common
import qualified Constant
import Core
import qualified Cps
import qualified Interpreter
import qualified Data.Text as T
import Lib
import qualified SystemF
import TextShow

iterTerm = 20

iterCbpv = 20

iterCallcc = 20

iterCps = 20

mkProgram :: SystemF.SystemF t => t SystemF.Term (F Integer)
mkProgram =
  SystemF.apply
    ( SystemF.lambda int $ \x ->
        SystemF.apply (SystemF.apply (SystemF.global plus) x) (SystemF.apply (SystemF.apply (SystemF.global plus) x) x)
    )
    (SystemF.constant (Constant.IntegerConstant 5))

phases ::
  SystemF.Term a ->
  ( SystemF.Term a,
    Cbpv.Code a,
    Cbpv.Code a,
    Cbpv.Code a,
    Callcc.Code a,
    Callcc.Code a,
    Cps.Data (Stack (F (Stack a))),
    Cps.Data (Stack (F (Stack a)))
  )
phases term =
  let optTerm = optimizeTerm term
      cbpv = Cbpv.build (toCallByPushValue optTerm)
      intrinsified = Cbpv.build (Cbpv.intrinsify cbpv)
      optIntrinsified = optimizeCbpv intrinsified
      catchThrow = toCallcc optIntrinsified
      optCatchThrow = optimizeCallcc catchThrow
      cps = Cps.build (toContinuationPassingStyle optCatchThrow)
      optCps = optimizeCps cps
   in (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps, optCps)

optimizeTerm :: SystemF.Term a -> SystemF.Term a
optimizeTerm = loop iterTerm
  where
    loop :: Int -> SystemF.Term a -> SystemF.Term a
    loop 0 term = term
    loop n term =
      let simplified = SystemF.build (SystemF.simplify term)
          inlined = SystemF.build (SystemF.inline simplified)
       in loop (n - 1) inlined

optimizeCbpv :: Cbpv.Code a -> Cbpv.Code a
optimizeCbpv = loop iterCbpv
  where
    loop :: Int -> Cbpv.Code a -> Cbpv.Code a
    loop 0 term = term
    loop n term =
      let simplified = Cbpv.simplify term
          inlined = Cbpv.build (Cbpv.inline simplified)
       in loop (n - 1) inlined

optimizeCallcc :: Callcc.Code a -> Callcc.Code a
optimizeCallcc = loop iterCallcc
  where
    loop :: Int -> Callcc.Code a -> Callcc.Code a
    loop 0 term = term
    loop n term =
      let simplified = Callcc.simplify term
          inlined = Callcc.build (Callcc.inline simplified)
       in loop (n - 1) inlined

optimizeCps :: Cps.Data a -> Cps.Data a
optimizeCps = loop iterCps
  where
    loop :: Int -> Cps.Data a -> Cps.Data a
    loop 0 term = term
    loop n term =
      let simplified = Cps.simplify term
          inlined = Cps.build (Cps.inline simplified)
       in loop (n - 1) inlined

main :: IO ()
main = do
  let program = SystemF.build $ mkProgram

  putStrLn "Lambda Calculus:"
  printT program

  let (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps, optCps) = phases program

  putStrLn "\nOptimized Term:"
  printT optTerm

  putStrLn "\nCall By Push Value:"
  printT cbpv

  putStrLn "\nIntrinsified:"
  printT intrinsified

  putStrLn "\nOptimized Intrinsified:"
  printT optIntrinsified

  putStrLn "\nCatch/Throw:"
  printT catchThrow

  putStrLn "\nOptimized Catch/Throw:"
  printT optCatchThrow

  putStrLn "\nCps:"
  printT cps

  putStrLn "\nOptimized Cps:"
  printT optCps

  let cpsData = Interpreter.evaluate optCps

  let PopStack k = cpsData
  let R eff = k $ PopStack $ \value -> R $ printT value
  eff

  return ()
