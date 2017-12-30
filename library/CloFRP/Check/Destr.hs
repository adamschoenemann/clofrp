{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.Check.Destr where

import CloFRP.AST
import Data.Data

-- A destructor which is elaborated from a pattern
data Destr a = Destr
  { name   :: Name
  , typ    :: PolyType a
  , bound  :: [(Name, Kind)]
  , args   :: [PolyType a]
  } deriving (Show, Eq, Data, Typeable)