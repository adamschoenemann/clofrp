{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}

module CloFRP.AST.Expr where

import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import qualified CloFRP.AST.Prim as P
import Data.Text.Prettyprint.Doc
import Control.DeepSeq
import GHC.Generics
import Data.Set (Set, (\\), union)
import qualified Data.Set as S

import CloFRP.Annotated
import CloFRP.AST.Name
import CloFRP.AST.Type
import CloFRP.AST.Pat
import CloFRP.AST.Utils


type Expr a = Annotated a (Expr' a)

data Expr' a
  -- | x
  = Var !Name 
  -- | [x]
  | TickVar !Name 
  -- | e : A
  | Ann (Expr a) (PolyType a) 
  -- | e1 e2
  | App (Expr a) (Expr a) 
  -- | \x -> e OR \(x : A) -> e
  | Lam Name (Maybe (PolyType a)) (Expr a) 
  -- | \\(α : κ) -> e
  | TickAbs !Name !Name (Expr a) 
  -- | n-ary tuples  
  | Tuple [Expr a] 
  -- | let p = e1 in e2  
  | Let (Pat a) (Expr a) (Expr a) 
  -- | case e of | p -> e | p1 -> e1 | pn -> en  
  | Case (Expr a) [(Pat a, Expr a)] 
  -- | e {A}  
  | TypeApp (Expr a) (PolyType a) 
  -- | fmap A  
  | Fmap (PolyType a) 
  -- | primRec A  
  | PrimRec (PolyType a) 
  -- | binary operators
  | BinOp Name (Expr a) (Expr a)
  -- | primitive (will probably just include ints in the end)  
  | Prim P.Prim 
  deriving (Eq, Data, Typeable, Generic, NFData)


data PrettyEP ann = PrettyEP
  { lamParens   :: Doc ann -> Doc ann
  , otherParens :: Doc ann -> Doc ann
  }


prettyE' :: PrettyEP ann -> Expr' a -> Doc ann
prettyE' (PrettyEP {lamParens, otherParens}) = \case
  Var nm -> pretty nm
  TickVar  nm -> brackets $ pretty nm
  Ann e t -> parens $ prettyE parlam e <+> ":" <+> pretty t
  App e1 e2 -> otherParens $ prettyE parlam e1 <+> prettyE (ep parens parens) e2

  Lam nm mty e ->
    let (ps', e') = collect pred e
        ps = (nm, mty) : ps'
        params = sep $ map rndrp ps
    in  lamParens $ "\\" <> params <+> "->" <> nest 2 (softline <> prettyE nopars e') where
      rndrp (nm, Nothing) = pretty nm
      rndrp (nm, Just ty) = parens (pretty nm <+> ":" <+> pretty ty)
      pred (Lam nm' mty' e'') = Just ((nm', mty'), e'')
      pred _                  = Nothing

  TickAbs  nm kappa e -> lamParens $ "\\\\" <> parens (pretty nm <+> ":" <+> pretty kappa) <+> "->" <+> pretty e

  Tuple es -> tupled (map (prettyE nopars) es)
  Let p e1 e2 -> align $ "let" <+> pretty p <+> "=" <+> group (pretty e1) <+> "in" <> softline <> pretty e2

  Case e clauses ->
    "case" <+> prettyE parlam e <+> "of" <> nest 2 (softline <> (sep $ map prettyC clauses))

  TypeApp e t -> otherParens (pretty e <+> braces (prettyT False t))
  Fmap t -> "fmap" <+> braces (pretty t)
  PrimRec t -> "primRec" <+> braces (pretty t)

  BinOp op e1 e2 -> parens (pretty e1 <+> pretty op <+> pretty e2)

  Prim p -> fromString . show $ p
  where
    prettyC (p, e) = "|" <+> pretty p <+> "->" <> nest 4 (softline <> (pretty e))
    nopars = PrettyEP id id
    parlam = PrettyEP parens otherParens
    ep x y = PrettyEP x y

prettyE :: PrettyEP ann -> Expr a -> Doc ann
prettyE n (A _ t) = prettyE' n t

instance Pretty (Expr' a) where
  pretty = prettyE' (PrettyEP id id)

instance Pretty (Expr a) where
  pretty (A _ t) = prettyE' (PrettyEP id id) t

instance Show (Expr' a) where
  show = show . pretty

instance IsString (Expr ()) where
  fromString input = A () $ case input of
    [] -> error "illegal empty name"
    xs
      | length xs > 2, head xs == '[', last xs == ']' -> TickVar . UName . tail . init $ xs
      | otherwise -> Var . UName $ xs

instance Unann (Expr a) (Expr ()) where
  unann = unannE

unannE :: Expr a -> Expr ()
unannE (A _ expr0) = A () (unannE' expr0)

instance Unann (Expr' a) (Expr' ()) where
  unann = unannE'

unannE' :: Expr' a -> Expr' ()
unannE' = \case
  Var nm      -> Var nm
  TickVar nm  -> TickVar nm
  Ann e t -> Ann (unannE e) (unannT t)
  App e1 e2 -> App (unannE e1) (unannE e2)
  Lam nm mty e -> Lam nm (unannT <$> mty) (unannE e)
  TickAbs nm kappa e -> TickAbs nm kappa (unannE e)
  Tuple es -> Tuple (map unannE es)
  Let p e1 e2 -> Let (unannPat p) (unannE e1) (unannE e2)
  Case e clauses -> Case (unannE e) $ map (\(p,c) -> (unannPat p, unannE c)) clauses
  TypeApp e t -> TypeApp (unannE e) (unannT t)
  Fmap t -> Fmap (unannT t)
  PrimRec t -> PrimRec (unannT t)
  BinOp nm e1 e2 -> BinOp nm (unannE e1) (unannE e2)
  Prim p -> Prim p

substExpr :: Expr' a -> Name -> Expr a -> Expr a
substExpr new old = go where 
  go (A ann into) = A ann $ case into of
    Var nm | nm == old -> new
           | otherwise -> Var nm
    TickVar nm | nm == old -> new
               | otherwise -> TickVar nm
    Ann e t -> Ann (go e) t
    App e1 e2 -> App (go e1) (go e2)
    Lam nm mty e 
      | nm == old -> Lam nm mty e
      | otherwise -> Lam nm mty (go e)
    TickAbs nm kappa e 
      | nm == old -> TickAbs nm kappa e
      | otherwise -> TickAbs nm kappa (go e)
    Tuple es -> Tuple (map go es)
    Let p e1 e2 -> Let p (go e1) (go e2)
    Case e clauses -> Case (go e) $ map (\(p,c) -> (p, go c)) clauses
    TypeApp e t -> TypeApp (go e) t
    Fmap t -> Fmap t
    PrimRec t -> PrimRec t
    BinOp nm e1 e2 -> BinOp nm (go e1) (go e2) -- replace operator names?
    Prim p -> Prim p

freeVarsExpr :: Expr a -> Set Name
freeVarsExpr = go where
  go (A _ expr') = case expr' of
    Var nm -> S.singleton nm
    TickVar nm -> S.singleton nm
    Ann e t -> go e 
    App e1 e2 -> go e1 `union` go e2
    Lam nm mty e -> go e \\ S.singleton nm
    TickAbs nm kappa e -> go e \\ S.singleton nm
    Tuple es -> S.unions (map go es)
    Let p e1 e2 -> go e1 `union` (go e2 \\ freeVarsPat p)
    Case e clauses -> go e `union` (S.unions $ map (\(p,e') -> go e' \\ freeVarsPat p) clauses)
    TypeApp e t -> go e
    Fmap t -> S.empty
    PrimRec t -> S.empty
    BinOp nm e1 e2 -> go e1 `union` go e2
    Prim p -> S.empty
