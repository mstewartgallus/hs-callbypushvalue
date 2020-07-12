{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (V, (:->), Pair, (:*:) (..), (:=>) (..), Unit (..), Void (..), F (..), U (..), R (..)) where

data V a b

type a :-> b = U a :=> b

infixr 9 :->

data Unit = Unit

newtype R = Behaviour (IO ())

newtype U a = Thunk (a -> R)

data a :*: b = a ::: b

infixr 0 :*:

infixr 0 :::

type Void = Unit

type F = U

type (:=>) = (:*:)

infixr 9 :=>

type Pair a b = F (a :*: b :*: Void)
