{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Box (Box) where

import GHC.Exts

data Box (k :: * -> Constraint)

-- mkProgram :: (forall t. k t => Code t a) -> Code (Box k) a
-- mkProgram = Program

-- interpret :: k t => Code (Box k) a -> Code t a
-- interpret (Program x) = x

-- instance HasData (Box k) where
--   newtype Data (Box k) a = Value (forall t. k t => Data t a)

-- mkValue :: (forall t. k t => Data t a) -> Data (Box k) a
-- mkValue = Value

-- interpretValue :: k t => Data (Box k) a -> Data t a
-- interpretValue (Value x) = x
