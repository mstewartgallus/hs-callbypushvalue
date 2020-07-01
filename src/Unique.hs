{-# LANGUAGE GADTs, RankNTypes #-}
module Unique (Unique, split, pick, stream) where
import System.IO.Unsafe
import TextShow
import Data.Atomics.Counter

newtype Unique = Unique Int deriving (Eq, Ord)

instance TextShow Unique where
  showb (Unique n) = fromString "v" <> showb n

newtype Supply = Supply (forall a. Choice a -> a)

data Choice a where
   Pick :: Choice (Unique, Supply)
   Split :: Choice (Supply, Supply)

split :: Supply -> (Supply, Supply)
split (Supply f) = f Split

pick :: Supply -> (Unique, Supply)
pick (Supply f) = f Pick

stream :: IO Supply
stream = let
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
             pure $ Supply $ \choice -> case choice of
                 Pick -> pick
                 Split -> split
  in do
     counter <- newCounter 0
     make counter
