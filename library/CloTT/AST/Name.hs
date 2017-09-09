{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Name where

import Data.Data
import Data.String (IsString(..))

data Name 
  = UName String
  | MName Integer
  deriving (Show, Ord, Eq, Data, Typeable)

instance IsString Name where
  fromString = UName