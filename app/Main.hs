module Main where

import qualified Callcc
import qualified Cbpv
import Control.Monad.State
import qualified Cps
import qualified Data.Text as T
import Lib
import SystemF
import qualified SystemF
import TextShow
import Unique

fixpoint :: (TextShow a, Eq a) => (a -> a) -> a -> a
fixpoint op = w 0
  where
    w 5000 term = error ("term did not terminate:\n" <> toString (showb term))
    w tick term =
      let newTerm = op term
       in if newTerm == term then term else w (tick + 1) newTerm

mkProgram :: Unique.Stream -> SystemF.Term (F Integer)
mkProgram =
  SystemF.build $
    SystemF.apply
      ( SystemF.lambda (ApplyType thunk int) $ \x ->
          SystemF.apply (SystemF.apply (SystemF.global plus) x) x
      )
      (SystemF.constant (IntegerConstant 5))

optimizeCbpv = inlineCbpv . simplifyCbpv

phases ::
  Unique.Stream ->
  SystemF.Term a ->
  ( SystemF.Term a,
    Cbpv.Code a,
    Cbpv.Code a,
    Cbpv.Code a,
    Cbpv.Code a,
    Callcc.Code a,
    Callcc.Code a,
    Cps.Code a
  )
phases (Unique.Split a (Unique.Split b (Unique.Split c d))) term =
  let optimizeTerm :: Unique.Stream -> Term a -> Term a
      optimizeTerm s t =
        let (left, right) = Unique.split s
            simplified = SystemF.build (SystemF.simplify t) left
            inlined = SystemF.build (SystemF.inline simplified) right
         in -- fixme.. get fixpoint working
            inlined
      optTerm = optimizeTerm a term
      cbpv = toCallByPushValue optTerm
      optCbpv = fixpoint optimizeCbpv cbpv
      intrinsified = Cbpv.build (intrinsify optCbpv) c
      optIntrinsified = fixpoint optimizeCbpv intrinsified
      catchThrow = toCallcc intrinsified b
      optCatchThrow = fixpoint simplifyCallcc catchThrow
      cps = Cps.build (toContinuationPassingStyle catchThrow) d
   in (optTerm, cbpv, optCbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps)

main :: IO ()
main = do
  stream <- Unique.streamIO
  let (left, right) = Unique.split stream
  let program = mkProgram left

  putStrLn "Lambda Calculus:"
  printT program

  let (optTerm, cbpv, optCbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps) = phases stream program

  putStrLn "\nOptimized Term:"
  printT optTerm

  putStrLn "\nCall By Push Value:"
  printT cbpv

  putStrLn "\nOptimized CBPV:"
  printT optCbpv

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

  Cps.evaluate cps $ \result -> do
    printT result

  return ()
