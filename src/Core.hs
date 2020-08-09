{-# LANGUAGE TypeOperators #-}

module Core
  ( minus,
    plus,
    strictPlus,
  )
where

import Common
import qualified Data.Text as T
import Global
import Name

plus :: Global (F U64 :-> F U64 :-> F U64)
plus = Global inferAlgebra $ Name (T.pack "core") (T.pack "+")

minus :: Global (F U64 :-> F U64 :-> F U64)
minus = Global inferAlgebra $ Name (T.pack "core") (T.pack "-")

strictPlus :: Global (U64 :=> U64 :=> F U64)
strictPlus = Global inferAlgebra $ Name (T.pack "core") (T.pack "+!")
