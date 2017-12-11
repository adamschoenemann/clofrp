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
{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.Eval.Value where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc 
import Control.DeepSeq
import GHC.Generics
import GHC.Exts
import Data.Data

import CloTT.AST.Name
import           CloTT.AST.Expr (Expr)
import qualified CloTT.AST.Expr as E

data PrimVal
  = IntVal Integer
  | Tick
  | RuntimeErr String
  deriving (Eq, Generic, NFData, Show, Data, Typeable)

instance Pretty PrimVal where
  pretty = \case
    IntVal i -> pretty i
    Tick     -> "[<>]"
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
  deriving (Show, Eq, Generic, NFData, Data, Typeable)

-- takes n levels down in a tree of constructors
takeConstr :: Int -> Value a -> Value a
takeConstr n v 
  | n < 0    = Prim $ RuntimeErr "Stopped evaling"
  | otherwise = 
      case v of
        Constr nm [] -> v
        Constr nm vs -> Constr nm (map (takeConstr (n-1)) vs)
        -- Constr nm vs -> Constr nm $ snd (foldr (\v' (n',acc) -> (n' - 1, takeConstr (n' - 1) v' : acc)) (n, []) vs)
        _            -> v

instance Pretty (Value a) where
  pretty value = case (takeConstr 10 value) of
    Prim p -> pretty p
    Var nm  -> pretty nm
    TickVar nm  -> pretty nm
    Closure env n e -> parens $ group $ "\\" <> pretty e <+> "->" <+> pretty e -- <> line <> indent 4 ("closed over" <+> pretty env)
    TickClosure env n e -> parens $ group $ "\\\\" <> pretty n <+> "->" <+> pretty e <> line <> indent 4 ("closed over" <+> pretty env)
    Tuple vs -> tupled (map pretty vs)
    Constr nm [] -> pretty nm
    Constr nm vs -> parens $ pretty nm <+> fillSep (map pretty vs)
    -- GetFmap e -> "__getfmap__" <+> parens (pretty e)

newtype Env a = Env {unEnv :: Map Name (Value a)}
  deriving newtype (Eq, Monoid)
  deriving stock (Generic, Data, Typeable)
  deriving anyclass NFData


instance Pretty (Env a) where
  pretty (Env e) = list $ M.elems $ M.mapWithKey (\k v -> pretty k <+> "↦" <+> align (pretty v)) e

instance Show (Env a) where
  show = show . pretty

extendEnv :: Name -> Value a -> Env a -> Env a
extendEnv k v = Env . M.insert k v . unEnv

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