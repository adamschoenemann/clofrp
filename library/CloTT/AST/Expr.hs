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

module CloTT.AST.Expr where

import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import qualified CloTT.AST.Prim as P
import Data.Text.Prettyprint.Doc
import Control.DeepSeq
import GHC.Generics

import CloTT.Annotated
import CloTT.AST.Name
import CloTT.AST.Type
import CloTT.AST.Pat
import CloTT.AST.Utils

type Expr a = Annotated a (Expr' a)

data Expr' a
  -- | x
  = Var Name 
  -- | [x]
  | TickVar Name 
  -- | e : A
  | Ann (Expr a) (Type a 'Poly) 
  -- | e1 e2
  | App (Expr a) (Expr a) 
  -- | \x -> e OR \(x : A) -> e
  | Lam Name (Maybe (Type a 'Poly)) (Expr a) 
  -- | \\(α : κ) -> e
  | TickAbs Name Name (Expr a) 
  -- | n-ary tuples  
  | Tuple [Expr a] 
  -- | let p = e1 in e2  
  | Let (Pat a) (Expr a) (Expr a) 
  -- | case e of | p -> e | p1 -> e1 | pn -> en  
  | Case (Expr a) [(Pat a, Expr a)] 
  -- | e {A}  
  | TypeApp (Expr a) (Type a 'Poly) 
  -- | fmap A  
  | Fmap (Type a 'Poly) 
  -- | primRec A  
  | PrimRec (Type a 'Poly) 
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
    "case" <+> prettyE parlam e <+> "of" <> softline <> (align $ sep $ map prettyC clauses)

  TypeApp e t -> otherParens (pretty e <+> braces (prettyT False t))
  Fmap t -> "fmap" <+> braces (pretty t)
  PrimRec t -> "primRec" <+> braces (pretty t)

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
  Prim p -> Prim p

