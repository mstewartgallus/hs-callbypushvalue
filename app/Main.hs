module Main where

import Lib
import Control.Monad.State
import TextShow
import qualified Data.Text as T

program :: Term (F Integer)
program = let
  x = Variable int (T.pack "x")
  in ApplyTerm (LambdaTerm x (ApplyTerm (ApplyTerm plus (VariableTerm x)) (VariableTerm x))) (ConstantTerm (IntegerConstant 5))

phases :: Term a -> (Code a, Code a, Code a, Action a, Stuff (Stack (F (Stack a))))
phases term = flip evalState (CompilerState 0 0) $ do
  let cpbv = toCallByPushValue term
  intrinsified <- intrinsify cpbv
  let simplified = simplifyCpbv intrinsified
  catchThrow <- toExplicitCatchThrow intrinsified
  cps <- toCps' catchThrow
  return (cpbv, intrinsified, simplified, catchThrow, cps)

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  printT program

  let (cpbv, intrinsified, simplified, catchThrow, cps) = phases program

  putStrLn "\nCall By Push Value:"
  printT cpbv

  putStrLn "\nIntrinsified:"
  printT intrinsified

  putStrLn "\nSimplified:"
  printT simplified

  putStrLn "\nCatch/Throw:"
  printT catchThrow

  putStrLn "\nCps:"
  printT cps
