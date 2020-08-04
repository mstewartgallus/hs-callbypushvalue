{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import qualified AsCbpv
import qualified AsCps
import qualified AsDup
import AsIntrinsified (AsIntrinsified)
import qualified AsIntrinsified
import qualified AsPorcelain
import AsText
import qualified Box
import Cbpv (Cbpv)
import qualified Cbpv
import Cbpv (HasThunk (..))
import qualified CbpvSimplifier
import Common
import qualified Constant
import Control.Category
import qualified Core
import qualified CostInliner
import CostInliner (CostInliner)
import qualified Cps
import Cps (Cps)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Word
import HasCall
import qualified Interpreter
import MonoInliner (MonoInliner)
import qualified MonoInliner
import NatTrans
import PairF
import SystemF (SystemF)
import qualified SystemF as F
import qualified SystemFSimplifier
import TextShow
import Prelude hiding ((.), id)

iterTerm = 20

iterCbpv = 20

iterCps = 20

program :: SystemF t => t (F U64 :-> F U64 :-> F U64)
program = F.lam $ \x ->
  F.lam $ \y ->
    ( F.lam $ \z ->
        call Core.plus F.<*> z F.<*> y
    )
      F.<*> (call Core.plus F.<*> F.constant (Constant.U64Constant 8) F.<*> y)

main :: IO ()
main = do
  copy <- dupLog program
  optTerm <- optimizeTerm copy
  cbpv <- cbpvTerm optTerm
  intrinsified <- intrinsify cbpv
  optCbpv <- optimizeCbpv intrinsified

  T.putStrLn (AsText.extract optCbpv)
  -- cps <- cpsTerm (Cbpv.thunk optCbpv)
  -- -- optCps <- optimizeCps cps

  -- let PairF porcelain interpreter = AsDup.extractData # cps

  -- putStrLn "\nPorcelain Output:"
  -- T.putStrLn (AsPorcelain.extract porcelain)

  -- putStrLn "\nEvaluates to:"
  -- let Interpreter.Thunk k = interpreter
  -- let Interpreter.Behaviour eff = k (t 4 `Interpreter.Apply` t 8 `Interpreter.Apply` (Interpreter.Returns $ \(Interpreter.I x) -> Interpreter.Behaviour $ printT x))
  -- eff

  return ()

type TextDupCode = AsDup.Code AsText.Code AsText.Data AsText.Stack

type TextDupData = AsDup.Data AsText.Code AsText.Data AsText.Stack

type TextDupStack = AsDup.Stack AsText.Code AsText.Data AsText.Stack

dupLog :: SystemF cd => TextDupCode cd dta k a -> IO (cd a)
dupLog term = do
  let PairF text copy = AsDup.extract # term

  putStrLn "Lambda Calculus:"
  T.putStrLn (AsText.extract text)

  return copy

cbpvTerm :: Cbpv cd dta => AsCbpv.Code (TextDupCode cd dta k) (TextDupData cd dta k) a -> IO (cd a)
cbpvTerm term = do
  let PairF text copy = (AsDup.extract . AsCbpv.extract) # term

  putStrLn "\nCall By Push Value:"
  T.putStrLn (AsText.extract text)

  return copy

intrinsify :: Cbpv cd dta => AsIntrinsified.Code (TextDupCode cd dta k) (TextDupData cd dta k) a -> IO (cd a)
intrinsify term = do
  let PairF text copy = (AsDup.extract . AsIntrinsified.extract) # term

  putStrLn "\nIntrinsified:"
  T.putStrLn (AsText.extract text)

  return copy

cpsTerm :: Cbpv cd dta => AsCps.Data (TextDupCode cd dta k) (TextDupData cd dta k) (TextDupStack cd dta k) a -> IO (dta a)
cpsTerm term = do
  let PairF text copy = (AsDup.extractData . AsCps.extract) # term

  putStrLn "\nContinuation Passing Style:"
  T.putStrLn (AsText.extractData text)

  return copy

type InlineCode cd dta k = MonoInliner.Code (CostInliner.Code cd dta k) (CostInliner.Data cd dta k) (CostInliner.Stack cd dta k)

type InlineData cd dta k = MonoInliner.Data (CostInliner.Code cd dta k) (CostInliner.Data cd dta k) (CostInliner.Stack cd dta k)

type OptF cd dta k = SystemFSimplifier.Code (InlineCode cd dta k)

-- fixme... loop

optimizeTerm :: SystemF cd => OptF (TextDupCode cd dta k) (TextDupData cd dta k) (TextDupStack cd dta k) a -> IO (cd a)
optimizeTerm input =
  let step :: SystemF cd => OptF cd dta k :~> cd
      step =
        CostInliner.extract
          . MonoInliner.extract
          . SystemFSimplifier.extract
   in do
        let PairF text copy = (AsDup.extract . step) # input
        putStrLn "\nOptimized Term:"
        T.putStrLn (AsText.extract text)

        return copy

-- loop :: Int -> Code (Box SystemF) a -> Code (Box SystemF) a
-- loop 0 term = term
-- loop n term = loop (n - 1) (mkProgram (step (Box.interpret term)))

type OptC cd dta k = CbpvSimplifier.Code (InlineCode cd dta k) (InlineData cd dta k)

-- fixme... loop
optimizeCbpv :: Cbpv cd dta => OptC (TextDupCode cd dta k) (TextDupData cd dta k) (TextDupStack cd dta k) a -> IO (cd a)
optimizeCbpv input =
  let step :: Cbpv cd dta => OptC cd dta k :~> cd
      step =
        CostInliner.extract
          . MonoInliner.extract
          . CbpvSimplifier.extract
   in do
        let PairF text copy = (AsDup.extract . step) # input
        putStrLn "\nOptimized Call By Push Value:"
        T.putStrLn (AsText.extract text)

        return copy

-- loop :: Int -> Data (Box Cbpv) a -> Data (Box Cbpv) a
-- loop 0 term = term
-- loop n term = loop (n - 1) (mkValue (step (Box.interpretValue term)))

-- type OptCps t = CpsSimplifier.Simplifier (MonoInliner (CostInliner t))

-- optimizeCps :: Cps cd dta k => OptCps (AsDup.Code AsText.Code AsText.Data AsText.Stack cd dta k)  (AsDup.Data AsText.Code AsText.Data AsText.Stack cd dta k) (AsDup.Stack AsText.Code AsText.Data AsText.Stack cd dta k) a -> IO (dta a)
-- optimizeCps input =
--   let step :: Cps cd dta k => OptCps cd dta k :~> dta
--       step =
--         CostInliner.extractData
--           . MonoInliner.extractData
--           . CpsSimplifier.extract
--    in do
--         let PairF text copy = (AsDup.extractData . step) # input
--         putStrLn "\nOptimized Continuation Passing Style:"
--         T.putStrLn (AsText.extractData text)

--         return copy

-- loop :: Int -> Data (Box Cps) a -> Data (Box Cps) a
-- loop 0 term = term
-- loop n term = loop (n - 1) (mkValue (step (Box.interpretValue term)))

t :: Word64 -> Interpreter.Value (U (F U64))
t x = Interpreter.Thunk $ \(Interpreter.Returns k) -> k (Interpreter.I x)
