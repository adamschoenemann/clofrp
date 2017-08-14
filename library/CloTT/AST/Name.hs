{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Name where

import Data.Data

data Name 
  = UName String
  deriving (Show, Eq, Data, Typeable)