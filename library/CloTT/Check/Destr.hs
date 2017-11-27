{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}

module CloTT.Check.Destr where

import CloTT.AST
import Data.Data

-- A destructor which is elaborated from a pattern
data Destr a = Destr
  { name   :: Name
  , typ    :: Type a Poly
  , bound  :: [(Name, Kind)]
  , args   :: [Type a Poly]
  } deriving (Show, Eq, Data, Typeable)