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

module CloTT.AST.Alias where

import Data.Data (Data, Typeable)
import Data.Text.Prettyprint.Doc

import CloTT.Annotated 
import CloTT.AST.Name
import CloTT.AST.Type

data Alias a = 
  Alias
    { alName :: Name
    , alBound :: [Name]
    , alExpansion :: Type a Poly
    } deriving (Show, Eq, Data, Typeable)


instance Unann (Alias a) (Alias ()) where
  unann al = al { alExpansion = unann (alExpansion al) }

instance Pretty (Alias a) where
  pretty (Alias {alName, alBound, alExpansion}) = "type" <+> pretty alName <> boundp <+> "=" <+> pretty alExpansion <> "."
    where boundp = if null alBound then "" else  " " <> (sep $ map pretty alBound)

  