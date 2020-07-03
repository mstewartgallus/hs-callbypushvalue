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

phases ::
  Unique.Stream ->
  SystemF.Term a ->
  ( SystemF.Term a,
    Cbpv.Code a,
    Cbpv.Code a,
    Cbpv.Code a,
    Callcc.Code a,
    Callcc.Code a,
    Cps.Code a
  )
phases (Unique.Split a (Unique.Split b (Unique.Split c (Unique.Split d e)))) term =
  let optimizeTerm :: Unique.Stream -> SystemF.Term a -> SystemF.Term a
      optimizeTerm = loop 50
        where
          loop :: Int -> Unique.Stream -> SystemF.Term a -> SystemF.Term a
          loop 0 _ term = term
          loop n (Unique.Split left (Unique.Split right strm)) term =
            let simplified = SystemF.build (SystemF.simplify term) left
                inlined = SystemF.build (SystemF.inline simplified) right
             in loop (n - 1) strm inlined
      optimizeCbpv :: Unique.Stream -> Cbpv.Code a -> Cbpv.Code a
      optimizeCbpv = loop 50
        where
          loop :: Int -> Unique.Stream -> Cbpv.Code a -> Cbpv.Code a
          loop 0 _ term = term
          loop n (Unique.Split left (Unique.Split right strm)) term =
            let simplified = Cbpv.simplify term
                inlined = Cbpv.build (Cbpv.inline simplified) right
             in loop (n - 1) strm inlined
      optTerm = optimizeTerm a term
      cbpv = toCallByPushValue optTerm
      intrinsified = Cbpv.build (intrinsify cbpv) b
      optIntrinsified = optimizeCbpv c intrinsified
      catchThrow = toCallcc intrinsified d
      optCatchThrow = fixpoint simplifyCallcc catchThrow
      cps = Cps.build (toContinuationPassingStyle catchThrow) e
   in (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps)

main :: IO ()
main = do
  stream <- Unique.streamIO
  let (left, right) = Unique.split stream
  let program = mkProgram left

  putStrLn "Lambda Calculus:"
  printT program

  let (optTerm, cbpv, intrinsified, optIntrinsified, catchThrow, optCatchThrow, cps) = phases stream program

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

  Cps.evaluate cps $ \result -> do
    printT result

  return ()
