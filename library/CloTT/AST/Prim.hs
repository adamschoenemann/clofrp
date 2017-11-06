{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Prim where

import Data.Data
import Prelude hiding (Bool, Int, Integer)
import qualified Prelude as Pr
import Data.Text.Prettyprint.Doc
import Data.String (fromString)

data Prim
  = Unit
  | Integer (Pr.Integer)
  | Fold 
  | Unfold
  | PrimRec
  | Tick
  | Fix
  | Undefined
  deriving (Eq, Data, Typeable)

instance Show Prim where
  show Unit    = "()"
  show (Integer x) = show x
  show Fold    = "fold"
  show Unfold  = "unfold"
  show PrimRec = "primRec"
  show Tick    = "◇"
  show Fix     = "fix"
  show Undefined  = "⊥"

instance Pretty Prim where
  pretty = fromString . show


