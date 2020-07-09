{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import qualified Callcc
import qualified Cbpv
import Common
import qualified Constant
import Core
import qualified Cps
import Data.Data
import qualified Data.Text as T
import qualified Interpreter
import Lib
import qualified SystemF
import TextShow
import Type

-- mkProgram :: (SystemF.SystemF t => Data a => t SystemF.Term a)
-- mkProgram = undefined

iterTerm = 20

iterCbpv = 20

iterCallcc = 20

iterCps = 20

mkProgram :: SystemF.SystemF t => t (F Integer :-> F Integer :-> F Integer)
mkProgram =
  SystemF.lambda (F IntType) $ \x ->
    SystemF.lambda (F IntType) $ \y ->
      SystemF.plus
        (SystemF.constant (Constant.IntegerConstant 4))
        (SystemF.plus y x)

phases ::
  SystemF.Term a ->
  ( SystemF.Term a,
    Cbpv.Code a,
    Cbpv.Code a,
    Cbpv.Code a,
    Callcc.Code a,
    Callcc.Code a,
    Cps.Term (U a),
    Cps.Term (U a)
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

optimizeCps :: Cps.Term a -> Cps.Term a
optimizeCps = loop iterCps
  where
    loop :: Int -> Cps.Term a -> Cps.Term a
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
  let MkR eff = k $ PushStack (t 4) $ PushStack (t 8) $ PopStack $ \value -> MkR $ printT value
  eff

  return ()

t :: a -> U (F a)
t x = PopStack $ \(PopStack k) -> k x
