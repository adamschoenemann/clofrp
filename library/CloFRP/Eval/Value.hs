{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CloFRP.Eval.Value where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Data.Text.Prettyprint.Doc
import GHC.Generics
import GHC.Exts
import Data.Data

import CloFRP.AST.Name
import           CloFRP.AST.Expr (Expr)
import qualified CloFRP.AST.Expr as E
import CloFRP.AST.Prim (Pntr)

data PrimVal
  = IntVal Integer
  | Tick
  | RuntimeErr String
  | FoldP
  | UnfoldP
  deriving (Eq, Generic, Show, Data, Typeable)

instance Pretty PrimVal where
  pretty = \case
    IntVal i -> pretty i
    Tick     -> "[<>]"
    FoldP     -> "foldP"
    UnfoldP     -> "unfoldP"
    RuntimeErr s -> "RUNTIMEERR:" <+> fromString s

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
  | Fold (Value a)
  | Delay (Value a)
  deriving (Show, Eq, Generic, Data, Typeable)

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
  pretty = prettyVal 4

prettyVal :: Int -> Value a -> Doc ann
prettyVal = pret where
  pret :: Int -> Value a -> Doc ann
  pret 0 _ = "..."
  pret i value =
    case (takeConstr 10 value) of
      Prim p -> pretty p
      Var nm  -> pretty nm
      TickVar nm  -> pretty nm
      Closure env n e -> parens $ group $ "\\" <> pretty n <+> "->" <+> pretty e -- <> line <> indent 4 ("closed over" <+> pret i env)
      TickClosure env n e ->
        let penv = if i > 0 then line <> indent 4 ("closed over" <+> prettyEnv i env)
                            else ""
        in  parens $ group $ "\\\\" <> pretty n <+> "->" <+> pretty e <> penv
      Tuple vs -> tupled (map (pret i) vs)
      Constr nm [] -> pretty nm
      Constr nm vs -> parens $ pretty nm <+> fillSep (map (pret (i-1)) vs)
      Fold v       -> parens $ "fold" <+> (pret i v)
      Delay v       -> parens $ "delay" <+> (pret i v)

prettyEnv :: Int -> Env a -> Doc ann
prettyEnv 0 _ = "..."
prettyEnv i (Env e) = list $ M.elems $ M.mapWithKey (\k v -> pretty k <+> "↦" <+> align (prettyVal (i-1) v)) e

newtype Env a = Env {unEnv :: Map Name (Value a)}
  deriving (Eq, Monoid, Generic, Data, Typeable)


instance Pretty (Env a) where
  pretty = prettyEnv 10

instance Show (Env a) where
  show = show . pretty

singleEnv :: Name -> Value a -> Env a
singleEnv n = Env . M.singleton n

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