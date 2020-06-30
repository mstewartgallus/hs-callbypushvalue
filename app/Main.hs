module Main where

import Lib
import Control.Monad.State
import TextShow
import qualified Data.Text as T

program :: Term (F Integer)
program = let
  x =  Variable int (T.pack "x")
  in ApplyTerm (LambdaTerm x $
                   ApplyTerm (ApplyTerm (GlobalTerm plus) (VariableTerm x)) (VariableTerm x)) (ConstantTerm (IntegerConstant 5))

phases :: Term a -> (Term a, Code a, Code a, Code a, Action a, Stuff (Stack (F (Stack a))))
phases term = flip evalState (CompilerState 0 0) $ do
  let simpleTerm = simplifyTerm term
  let cpbv = toCallByPushValue simpleTerm
  intrinsified <- intrinsify cpbv
  let simplified = simplifyCpbv intrinsified
  catchThrow <- toExplicitCatchThrow intrinsified
  cps <- toCps' catchThrow
  return (simpleTerm, cpbv, intrinsified, simplified, catchThrow, cps)

main :: IO ()
main = do
  putStrLn "Lambda Calculus:"
  printT program

  let (simpleTerm, cpbv, intrinsified, simplified, catchThrow, cps) = phases program

  putStrLn "\nSimplifed Term:"
  printT simpleTerm

  putStrLn "\nCall By Push Value:"
  printT cpbv

  putStrLn "\nIntrinsified:"
  printT intrinsified

  putStrLn "\nSimplified CBPV:"
  printT simplified

  putStrLn "\nCatch/Throw:"
  printT catchThrow

  putStrLn "\nCps:"
  printT cps
