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
program = let
  x =  Variable (Type undefined) (T.pack "x")
  in ApplyTerm (LambdaTerm x $
                   ApplyTerm (ApplyTerm (GlobalTerm plus) (VariableTerm x)) (VariableTerm x)) (ConstantTerm (IntegerConstant 5))

phases :: Term a -> (Term a, Code a, Code a, Code a, Action a, Action a, Stuff (Stack (F (Stack a))))
phases term = flip evalState (CompilerState 0 0) $ do
  let optTerm = fixpoint (inlineTerm . simplifyTerm) term

  let cbpv = toCallByPushValue optTerm
  intrinsified <- intrinsify cbpv
  let optCbpv = fixpoint simplifyCbpv intrinsified

  catchThrow <- toExplicitCatchThrow intrinsified
  let optCatchThrow = simplifyCallcc catchThrow

  cps <- toCps' catchThrow

  return (optTerm, cbpv, intrinsified, optCbpv, catchThrow, optCatchThrow, cps)

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  printT program

  let (optTerm, cbpv, intrinsified, optCbpv, catchThrow, optCatchThrow, cps) = phases program

  putStrLn "\nOptimized Term:"
  printT optTerm

  putStrLn "\nCall By Push Value:"
  printT cbpv

  putStrLn "\nIntrinsified:"
  printT intrinsified

  putStrLn "\nOptimized CBPV:"
  printT optCbpv

  putStrLn "\nCatch/Throw:"
  printT catchThrow

  putStrLn "\nOptimized Catch/Throw:"
  printT optCatchThrow

  putStrLn "\nCps:"
  printT cps
