{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.AST.Synonym where

import Data.Data (Data, Typeable)
import Data.Text.Prettyprint.Doc

import CloFRP.Annotated 
import CloFRP.AST.Name
import CloFRP.AST.Type
import CloFRP.AST.Kind

data Synonym a = 
  Synonym
    { alName :: Name
    , alBound :: [(Name, Kind)]
    , alExpansion :: Type a 'Poly
    } deriving (Show, Eq, Data, Typeable)


instance Unann (Synonym a) (Synonym ()) where
  unann al = al { alExpansion = unann (alExpansion al) }

instance Pretty (Synonym a) where
  pretty (Synonym {alName, alBound, alExpansion}) = "type" <+> pretty alName <> boundp <+> "=" <+> pretty alExpansion
    where boundp = if null alBound then "" else  " " <> (sep $ map (uncurry $ prettyBound True) alBound)

  