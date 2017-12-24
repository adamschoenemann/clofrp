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
    { synName :: Name
    , synBound :: [(Name, Kind)]
    , synExpansion :: Type a 'Poly
    } deriving (Show, Eq, Data, Typeable)


instance Unann (Synonym a) (Synonym ()) where
  unann syn = syn { synExpansion = unann (synExpansion syn) }

instance Pretty (Synonym a) where
  pretty (Synonym {synName, synBound, synExpansion}) = "type" <+> pretty synName <> boundp <+> "=" <+> pretty synExpansion
    where boundp = if null synBound then "" else  " " <> (sep $ map (uncurry $ prettyBound True) synBound)

  