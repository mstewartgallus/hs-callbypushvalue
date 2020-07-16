{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

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
plus = Global (SU (SF SU64) `SFn` SU (SF SU64) `SFn` SF SU64) $ Name (T.pack "core") (T.pack "+")

minus :: Global (F U64 :-> F U64 :-> F U64)
minus = Global (SU (SF SU64) `SFn` SU (SF SU64) `SFn` SF SU64) $ Name (T.pack "core") (T.pack "-")

strictPlus :: Global (U64 :=> U64 :=> F U64)
strictPlus = Global (SU64 `SFn` SU64 `SFn` SF SU64) $ Name (T.pack "core") (T.pack "+!")
