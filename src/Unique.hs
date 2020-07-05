{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}

module Unique (Unique, run, uniqueId, Stream, pattern Pick, pattern Split, State, split, pick, stream, streamIO) where

import Data.Atomics.Counter
import GHC.Exts ((+#), Int (I#), Int#)
import System.IO.Unsafe
import TextShow

newtype State a = State (Int# -> (# Int#, a #))

run :: State a -> a
run (State f) =
  let (# _, x #) = f 0#
   in x

instance Functor State where
  fmap f (State g) = State $ \s ->
    let (# s', x #) = g s
        y = f x
     in (# s', y #)

instance Applicative State where
  pure x = State $ \s -> (# s, x #)
  State f <*> State x = State $ \s0 ->
    let (# s1, f' #) = f s0
        (# s2, x' #) = x s1
        y = f' x'
     in (# s2, y #)

instance Monad State where
  (State x) >>= f = State $ \s0 ->
    let (# s1, x' #) = x s0
        State y = f x'
     in y s1

uniqueId :: State Unique
uniqueId = State $ \ids -> (# ids +# 1#, Unique (I# ids) #)

newtype Unique = Unique Int deriving (Eq, Ord)

instance TextShow Unique where
  showb (Unique n) = fromString "v" <> showb n

newtype Stream = Stream (forall a. Choice a -> a)

data Choice a where
  PickChoice :: Choice (Unique, Stream)
  SplitChoice :: Choice (Stream, Stream)

split :: Stream -> (Stream, Stream)
split (Stream f) = f SplitChoice

pick :: Stream -> (Unique, Stream)
pick (Stream f) = f PickChoice

-- fixme.. not sure is safe
stream :: (Stream -> a) -> a
stream f = unsafePerformIO $ do
  s <- streamIO
  pure (f s)

streamIO :: IO Stream
streamIO =
  let make counter = loop
        where
          uniqueId = do
            c <- incrCounter 1 counter
            pure (c - 1)
          loop = do
            pick <- unsafeInterleaveIO $ do
              h <- uniqueId
              t <- loop
              return (Unique h, t)
            split <- unsafeInterleaveIO $ do
              l <- loop
              r <- loop
              return (l, r)
            pure $ Stream $ \choice -> case choice of
              PickChoice -> pick
              SplitChoice -> split
   in do
        counter <- newCounter 0
        make counter

pattern Pick head tail <- (Unique.pick -> (head, tail))

pattern Split left right <- (Unique.split -> (left, right))
