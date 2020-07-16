{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Duplicate (extract, Dup (..)) where

import Basic
import Common
import qualified Constant
import Core
import Global
import qualified SystemF as F

extract :: AlgRep (Dup x y) a -> (AlgRep x a, AlgRep y a)
extract (Dup x y) = (x, y)

data Dup x y

instance (Basic x, Basic y) => Basic (Dup x y) where
  data AlgRep (Dup x y) a = Dup (AlgRep x a) (AlgRep y a)
  global g = Dup (global g) (global g)

instance (F.SystemF x, F.SystemF y) => F.SystemF (Dup x y) where
  constant k = Dup (F.constant k) (F.constant k)

  pair (Dup x x') (Dup y y') = Dup (F.pair x y) (F.pair x' y')

  letBe (Dup x y) f = Dup left right
    where
      left = F.letBe x $ \x' ->
        let Dup body _ = f (Dup x' y)
         in body
      right = F.letBe y $ \y' ->
        let Dup _ body = f (Dup x y')
         in body
  lambda t f = Dup left right
    where
      left = F.lambda t $ \x ->
        -- fixme... is a better probe possible ?
        let Dup body _ = f (Dup x undefined)
         in body
      right = F.lambda t $ \x ->
        let Dup _ body = f (Dup undefined x)
         in body
  Dup f f' <*> Dup x x' = Dup (f F.<*> x) (f' F.<*> x')
