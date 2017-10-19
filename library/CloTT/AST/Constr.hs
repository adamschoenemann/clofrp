{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

module CloTT.AST.Constr where

import Data.Data (Data, Typeable)
import Data.Text.Prettyprint.Doc

import CloTT.Annotated 
import CloTT.AST.Name
import CloTT.AST.Type

type Constr a = Annotated a (Constr' a)
data Constr' a
  = Constr Name [Type a Poly]

instance Pretty (Constr a) where
  pretty (A _ c) = prettyC c where
    prettyC (Constr nm ps) = pretty nm <+> sep (map pretty ps)

deriving instance Show a     => Show (Constr' a)
deriving instance Eq a       => Eq (Constr' a)
deriving instance Data a     => Data (Constr' a)
deriving instance Typeable a => Typeable (Constr' a)

instance Unann (Constr a) (Constr ()) where
  unann = unannConstr

unannConstr :: Constr a -> Constr ()
unannConstr (A _ c) =
  case c of
    Constr nm ts -> A () $ Constr nm (map unannT ts)