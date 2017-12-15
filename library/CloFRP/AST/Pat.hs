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

module CloFRP.AST.Pat where

import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import Data.Char (isUpper)
import Data.Text.Prettyprint.Doc
import Control.DeepSeq
import GHC.Generics

import CloFRP.Annotated 
import CloFRP.AST.Name

type Pat a = Annotated a (Pat' a)
data Pat' a  
  = Bind Name 
  | Match Name [Pat a]
  | PTuple [Pat a]
  deriving (Eq, Data, Typeable, Generic, Typeable, NFData)

prettyP :: Bool -> Pat a -> Doc ann
prettyP n (A _ t) = prettyP' n t

prettyP' :: Bool -> Pat' a -> Doc ann
prettyP' pars = \case
  Bind nm -> pretty nm
  Match nm []   -> pretty nm
  Match nm pats -> parensIf $ pretty nm <+> hsep (map (prettyP False) pats)
  PTuple   pats -> tupled (map (prettyP False) pats)
  where
    parensIf = if pars then parens else id

instance Pretty (Pat' a) where
  pretty = prettyP' False

instance Pretty (Pat a) where
  pretty (A _ t) = prettyP' False t

instance Show (Pat' a) where
  show = show . pretty

instance IsString (Pat ()) where
  fromString nm 
    | isUpper $ head nm = error "Pat.fromString must be given a lower-chase string"
    | otherwise         = A () . Bind . UName $ nm

instance Unann (Pat a) (Pat ()) where
  unann = unannPat

unannPat :: Pat a -> Pat ()
unannPat (A _ p) = A () $ unannPat' p

instance Unann (Pat' a) (Pat' ()) where
  unann = unannPat'

unannPat' :: Pat' a -> Pat' ()
unannPat' p = case p of
  Bind nm -> Bind nm
  Match nm ps ->  Match nm (map unannPat ps)
  PTuple ps -> PTuple (map unannPat ps)