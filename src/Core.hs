{-# LANGUAGE TypeOperators #-}

module Core
  ( minus,
    plus,
  )
where

import qualified Data.Text as T
import Global
import Name
import SystemF.Type

plus :: Global (U64 ~> U64 ~> U64)
plus = Global inferType $ Name (T.pack "core") (T.pack "+")

minus :: Global (U64 ~> U64 ~> U64)
minus = Global inferType $ Name (T.pack "core") (T.pack "-")

-- strictPlus :: Global (U64 ~> U64 ~> F U64)
-- strictPlus = Global inferAlgebra $ Name (T.pack "core") (T.pack "+!")
