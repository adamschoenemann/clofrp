{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module CloFRP.AST.Prim where

import Data.Data
import Prelude hiding (Bool, Int, Integer)
import qualified Prelude as Pr
import Data.String (fromString)
import Control.DeepSeq
import GHC.Generics
import CloFRP.Pretty

type Pntr = Pr.Integer

data Prim
  = Unit
  | Integer (Pr.Integer)
  | Fold
  | Unfold
  -- | PrimRec
  | Tick
  | Fix
  | Undefined
  | Input
  | PntrDeref Pntr
  deriving (Eq, Data, Typeable, Generic, NFData)

instance Show Prim where
  show Unit    = "()"
  show (Integer x) = show x
  show Fold    = "fold"
  show Unfold  = "unfold"
  -- show PrimRec = "primRec"
  show Tick    = "◇"
  show Fix     = "fix"
  show Undefined  = "⊥"
  show Input  = "#input"
  show (PntrDeref p)  = "!" ++ show p

instance Pretty Prim where
  pretty = fromString . show
