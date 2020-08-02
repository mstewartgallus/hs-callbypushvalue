{-# LANGUAGE PolyKinds #-}

module PairF (PairF (..)) where

data PairF f g x = PairF (f x) (g x)
