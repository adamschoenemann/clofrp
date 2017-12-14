{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.AST.Alias where

import Data.Data (Data, Typeable)
import Data.Text.Prettyprint.Doc

import CloFRP.Annotated 
import CloFRP.AST.Name
import CloFRP.AST.Type
import CloFRP.AST.Kind

data Alias a = 
  Alias
    { alName :: Name
    , alBound :: [(Name, Kind)]
    , alExpansion :: Type a 'Poly
    } deriving (Show, Eq, Data, Typeable)


instance Unann (Alias a) (Alias ()) where
  unann al = al { alExpansion = unann (alExpansion al) }

instance Pretty (Alias a) where
  pretty (Alias {alName, alBound, alExpansion}) = "type" <+> pretty alName <> boundp <+> "=" <+> pretty alExpansion
    where boundp = if null alBound then "" else  " " <> (sep $ map (uncurry $ prettyBound True) alBound)

  