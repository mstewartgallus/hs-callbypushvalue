{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}

module Unique (Unique, run, uniqueId, withStream, State, Stream (..)) where

import Data.Atomics.Counter
import GHC.Exts (Int (I#), Int#, (+#))
import System.IO.Unsafe
import TextShow

-- fixme... consider existentialy tp allow a withStream operation ?
data Stream s = Stream Unique (Stream s) (Stream s)

withStream :: (forall s. Stream s -> b) -> b
withStream f = unsafePerformIO $ do
  s <- stream
  return (f s)

stream :: IO (Stream s)
stream = do
  counter <- newCounter 0
  stream' counter

stream' :: AtomicCounter -> IO (Stream s)
stream' counter = unsafeInterleaveIO $ do
  u <- unique counter
  x <- stream' counter
  y <- stream' counter
  return (Stream u x y)

unique :: AtomicCounter -> IO Unique
unique counter = do
  x <- incrCounter 1 counter
  return (Unique (x - 1))

newtype State a = State (Int# -> (# Int#, a #))

run :: State a -> a
run (State f) =
  let !(# _, x #) = f 0#
   in x

instance Functor State where
  fmap f (State g) = State $ \s ->
    let !(# s', x #) = g s
        y = f x
     in (# s', y #)

instance Applicative State where
  pure x = State $ \s -> (# s, x #)
  State f <*> State x = State $ \s0 ->
    let !(# s1, f' #) = f s0
        !(# s2, x' #) = x s1
        y = f' x'
     in (# s2, y #)

instance Monad State where
  (State x) >>= f = State $ \s0 ->
    let !(# s1, x' #) = x s0
        State y = f x'
     in y s1

uniqueId :: State Unique
uniqueId = State $ \ids -> (# ids +# 1#, Unique (I# ids) #)

newtype Unique = Unique Int deriving (Eq, Ord)

instance TextShow Unique where
  showb (Unique n) = showb n

instance Show Unique where
  show u = toString (showb u)
