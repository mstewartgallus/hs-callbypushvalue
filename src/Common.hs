{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (V, (:->), F, U, R (..), Stack (..)) where

data V a b

type a :-> b = U a -> b

infixr 9 :->

data R

data F a

type U a = Stack (F (Stack a))

data Stack a where
  PopStack :: (a -> IO ()) -> Stack (F a)
  PushStack :: a -> Stack b -> Stack (a -> b)
