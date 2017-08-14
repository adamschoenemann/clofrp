{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Prim where

import Data.Data
import Prelude hiding (Bool, Int, Integer)
import qualified Prelude as Pr

data Prim
  = Unit
  | Bool (Pr.Bool)
  | Nat (Pr.Integer)
  deriving (Show, Eq, Data, Typeable)