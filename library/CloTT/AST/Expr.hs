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

module CloTT.AST.Expr where

import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import qualified CloTT.AST.Prim as P
import Data.Text.Prettyprint.Doc

import CloTT.Annotated 
import CloTT.AST.Name
import CloTT.AST.Type
import CloTT.AST.Pat

type Expr a = Annotated a (Expr' a)

data Expr' a
  = Var Name
  | Ann (Expr a) (Type a Poly)
  | App (Expr a) (Expr a)
  | Lam Name (Maybe (Type a Poly)) (Expr a)
  | Tuple (Expr a) (Expr a)
  | Case (Expr a) [(Pat a, Expr a)]
  | Prim P.Prim
 
deriving instance Eq a       => Eq (Expr' a)
deriving instance Data a     => Data (Expr' a)
deriving instance Typeable a => Typeable (Expr' a)
-- deriving instance Show a     => Show (Expr' a)

prettyE' :: Bool -> Expr' a -> Doc ann
prettyE' pars = \case 
  Var nm -> pretty nm
  Ann e t -> parensIf $ "the" <+> parens (pretty t) <+> prettyE False e
  App e1 e2 -> parensIf $ prettyE False e1 <+> prettyE True e2

  Lam nm mty e -> 
    let tyann = maybe "" (\t -> space <> ":" <+> pretty t) mty
    in  parensIf $ "λ" <> pretty nm <> tyann <+> "->" <+> prettyE False e

  Tuple e1 e2 -> parens (prettyE False e1 <> comma <+> prettyE False e2)

  Case e clauses ->
    "case" <+> prettyE False e <+> "of" <> softline <> (align $ sep $ map prettyC clauses)

  Prim p -> fromString . show $ p
  where
    prettyC (p, e) = "|" <+> pretty p <+> "->" <+> pretty e
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
  fromString = A () . Var . UName

instance Unann (Expr a) (Expr ()) where
  unann = unannE

unannE :: Expr a -> Expr ()
unannE (A _ expr0) = A () (unannE' expr0)

instance Unann (Expr' a) (Expr' ()) where
  unann = unannE'

unannE' :: Expr' a -> Expr' ()
unannE' = \case
  Var nm -> Var nm
  Ann e t -> Ann (unannE e) (unannT t)
  App e1 e2 -> App (unannE e1) (unannE e2)
  Lam nm mty e -> Lam nm (unannT <$> mty) (unannE e)
  Tuple e1 e2 -> Tuple (unannE e1) (unannE e2)
  Case e clauses -> Case (unannE e) $ map (\(p,c) -> (unannPat p, unannE c)) clauses
  Prim p -> Prim p