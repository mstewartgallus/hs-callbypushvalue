module Main where

import Lib
import Control.Monad.State
import TextShow
import qualified Data.Text as T

fixpoint :: (TextShow a, Eq a) => (a -> a) -> a -> a
fixpoint op = w 0 where
  w 5000 term = error ("term did not terminate:\n" <> toString (showb term))
  w tick term = let
    newTerm = op term
    in if newTerm == term then term else w (tick + 1) newTerm

program :: Term (F Integer)
program = ApplyTerm (LambdaTerm (Type undefined) $ \x ->
          ApplyTerm (ApplyTerm (GlobalTerm plus)  x) x) (ConstantTerm (IntegerConstant 5))

optimizeCbpv = inlineCbpv . simplifyCbpv

phases ::  Term a -> (Term a, Code a, Code a, Code a, Code a, Action a, Action a, Stuff (Stack (F (Stack a))))
phases term = flip evalState (CompilerState 0 0) $ do
  let optTerm = fixpoint (inlineTerm . simplifyTerm) term

  cbpv <- toCallByPushValue optTerm

  let optCbpv = fixpoint optimizeCbpv cbpv
  intrinsified <- intrinsify optCbpv
  let optIntrinsified = fixpoint optimizeCbpv intrinsified

  catchThrow <- toExplicitCatchThrow intrinsified
  let optCatchThrow = fixpoint simplifyCallcc catchThrow

  cps <- toCps' catchThrow

  return (optTerm, cbpv, optCbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps)

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  printT program

  let (optTerm, cbpv, optCbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps) = phases program

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
