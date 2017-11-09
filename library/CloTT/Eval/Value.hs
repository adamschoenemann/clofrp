{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module CloTT.Eval.Value where

import Data.Map.Strict (Map)
import qualified Data.Map as M
import Data.Text.Prettyprint.Doc 
import Control.DeepSeq
import GHC.Generics
import GHC.Exts

import CloTT.AST.Name
import           CloTT.AST.Expr (Expr)
import qualified CloTT.AST.Expr as E

data PrimVal
  = IntVal Integer
  | Tick
  | Fold
  | Unfold
  | PrimRec
  | Fix 
  | RuntimeErr String
  deriving (Eq, Generic, NFData, Show)

instance Pretty PrimVal where
  pretty = \case
    IntVal i -> pretty i
    Tick     -> "[<>]"
    Fold     -> "fold"
    Unfold   -> "unfold"
    PrimRec  -> "primRec"
    Fix      -> "fix"
    RuntimeErr s -> fromString s

-- instance Show PrimVal where show = show . pretty

-- |A Value is an expression that is evaluated to normal form
data Value a
  = Prim PrimVal
  | Var Name
  | TickVar Name
  | Closure (Env a) Name (Expr a)
  | TickClosure (Env a) Name (Expr a)
  | Tuple [Value a]
  | Constr Name [Value a]
  deriving (Show, Eq, Generic, NFData)

instance Pretty (Value a) where
  pretty = \case
    Prim p -> pretty p
    Var nm  -> pretty nm
    TickVar nm  -> pretty nm
    Closure env n e -> parens $ group $ "\\" <> pretty e <+> "->" <+> pretty e -- <> line <> indent 4 ("closed over" <+> pretty env)
    TickClosure env n e -> parens $ group $ "\\\\" <> pretty n <+> "->" <+> pretty e <> line <> indent 4 ("closed over" <+> pretty env)
    Tuple vs -> tupled (map pretty vs)
    Constr nm [] -> pretty nm
    Constr nm vs -> parens $ pretty nm <+> fillSep (map pretty vs)

newtype Env a = Env {unEnv :: Map Name (Value a)}
  deriving newtype (Eq, Monoid)
  deriving stock Generic
  deriving anyclass NFData


instance Pretty (Env a) where
  pretty (Env e) = list $ M.elems $ M.mapWithKey (\k v -> pretty k <+> "↦" <+> align (pretty v)) e

instance Show (Env a) where
  show = show . pretty

extend :: Name -> Value a -> Env a -> Env a
extend k v = Env . M.insert k v . unEnv

combine :: Env a -> Env a -> Env a
combine (Env x) (Env y) = Env $ M.union x y 

combineMany :: [Env a] -> Env a
combineMany = Env . M.unions . map unEnv

envLookup :: Name -> Env a -> Maybe (Value a)
envLookup n (Env x) = M.lookup n x

instance (IsList (Env a)) where
  type Item (Env a) = (Name, Value a)
  fromList xs = Env $ M.fromList xs
  toList (Env m) = M.toList m