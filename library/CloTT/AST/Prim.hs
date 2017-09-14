{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Prim where

import Data.Data
import Prelude hiding (Bool, Int, Integer)
import qualified Prelude as Pr
import Data.Text.Prettyprint.Doc
import Data.String (fromString)

data Prim
  = Unit
  | Bool (Pr.Bool)
  | Nat (Pr.Integer)
  deriving (Eq, Data, Typeable)

instance Show Prim where
  show Unit = "()"
  show (Bool x) = show x
  show (Nat x)  = show x

instance Pretty Prim where
  pretty = fromString . show


