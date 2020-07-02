{-# LANGUAGE GADTs, RankNTypes, ViewPatterns, PatternSynonyms #-}
module Unique (Unique, Stream, pattern Pick, pattern Split, split, pick, stream, streamIO) where
import System.IO.Unsafe
import TextShow
import Data.Atomics.Counter

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
streamIO = let
    make counter = loop where
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
