{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module CloTT.AST.Prim where

import Data.Data
import Prelude hiding (Bool, Int, Integer)
import qualified Prelude as Pr
import Data.Text.Prettyprint.Doc
import Data.String (fromString)
import Control.DeepSeq
import GHC.Generics
import CloTT.AST.Type

data Prim
  = Unit
  | Integer (Pr.Integer)
  | Fold
  | Unfold
  | PrimRec
  | Tick
  | Fix
  | Undefined
  | Fmap
  deriving (Eq, Data, Typeable, Generic, NFData)

instance Show Prim where
  show Unit    = "()"
  show (Integer x) = show x
  show Fold    = "fold"
  show Unfold  = "unfold"
  show PrimRec = "primRec"
  show Tick    = "◇"
  show Fix     = "fix"
  show Undefined  = "⊥"
  show Fmap  = "__fmap__"

instance Pretty Prim where
  pretty = fromString . show


