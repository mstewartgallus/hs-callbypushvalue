{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (V, (:->), F, U, Nil, R (..), Stack (..)) where

data V a b

type a :-> b = U a -> b

infixr 9 :->

newtype R = R (IO ())

data F a

type U a = Stack (F (Stack a))

data Nil

data Stack a where
  NilStack :: Stack Nil
  PopStack :: (a -> R) -> Stack (F a)
  PushStack :: a -> Stack b -> Stack (a -> b)
