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
  = Var Name -- a
  | TickVar Name -- [a]
  | Ann (Expr a) (Type a Poly) -- the τ a
  | App (Expr a) (Expr a) -- e1 e2
  | Lam Name (Maybe (Type a Poly)) (Expr a) -- λx -> e OR λ(x : A) -> e
  | TickAbs Name Name (Expr a) -- λ(α : κ) -> e
  | Tuple [Expr a] -- n-ary tuples
  | Let (Pat a) (Expr a) (Expr a) -- let p = e1 in e2
  | Case (Expr a) [(Pat a, Expr a)] -- case e of | p -> e | p1 -> e1 | pn -> en
  | TypeApp (Expr a) (Type a Poly) -- e {τ}
  | Prim P.Prim -- primitive (will probably just include ints in the end)
  deriving (Eq, Data, Typeable, Generic, NFData)

prettyE' :: Bool -> Expr' a -> Doc ann
prettyE' pars = \case 
  Var nm -> pretty nm
  TickVar  nm -> brackets $ pretty nm
  Ann e t -> parens $ prettyE False e <+> ":" <+> pretty t
  App e1 e2 -> parensIf $ prettyE False e1 <+> prettyE True e2

  Lam nm mty e -> 
    let (ps', e') = collect pred e
        ps = (nm, mty) : ps'
        params = sep $ map rndrp ps
    in  parensIf $ "\\" <> params <+> "->" <> nest 2 (softline <> prettyE False e') where
      rndrp (nm, Nothing) = pretty nm
      rndrp (nm, Just ty) = parens (pretty nm <+> ":" <+> pretty ty)
      pred (Lam nm' mty' e'') = Just ((nm', mty'), e'')
      pred _                  = Nothing
  
  TickAbs  nm kappa e -> parens $ "\\\\" <> parens (pretty nm <+> ":" <+> pretty kappa) <+> "->" <+> pretty e

  Tuple es -> tupled (map (prettyE False) es)
  Let p e1 e2 -> align $ "let" <+> pretty p <+> "=" <+> group (pretty e1) <+> "in" <> softline <> pretty e2

  Case e clauses ->
    "case" <+> prettyE False e <+> "of" <> softline <> (align $ sep $ map prettyC clauses)
  
  TypeApp e t -> parensIf (pretty e <+> braces (prettyT False t))

  Prim p -> fromString . show $ p
  where
    prettyC (p, e) = "|" <+> pretty p <+> "->" <> nest 4 (softline <> (pretty e))
    parensIf = if pars then parens else id

prettyE :: Bool -> Expr a -> Doc ann
prettyE n (A _ t) = prettyE' n t

instance Pretty (Expr' a) where
  pretty = prettyE' False

instance Pretty (Expr a) where
  pretty (A _ t) = prettyE' False t

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
  Prim p -> Prim p
