{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Common (V, (:->), Pair, (:*:) (..), (:=>) (..), Unit (..), Void (..), F (..), U (..)) where

-- First define the basic recursive data types.
data V a b

data Unit

data U a

data a :*: b

infixr 0 :*:

-- Then define the dual types as type synonyms
type Void = Unit

type F = U

-- Then define the call by name sugarings
type a :-> b = U a :=> b

infixr 9 :->

type (:=>) = (:*:)

infixr 9 :=>

type Pair a b = F (U a :*: U b :*: Unit)
