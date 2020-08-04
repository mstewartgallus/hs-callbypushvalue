{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasStack (HasStack (..)) where

import Common

class HasStack t where
  data Stack t :: Algebra -> *
