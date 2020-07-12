{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (V, (:->), Pair, (:*:) (..), (:=>) (..), Unit (..), Void (..), F (..), U (..), R (..)) where

-- First define the basic recursive data types.
data V a b

data Unit = Unit

newtype U a = Thunk (a -> R)

data a :*: b = a ::: b

infixr 0 :*:

infixr 0 :::

-- Then define the dual types as type synonyms
type Void = Unit

type F = U

-- R is an implementation detail basically
newtype R = Behaviour (IO ())

-- Then define the call by name sugarings
type a :-> b = U a :=> b

infixr 9 :->

type (:=>) = (:*:)

infixr 9 :=>

type Pair a b = F (U a :*: U b :*: Unit)
