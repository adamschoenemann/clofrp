{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Kind where

import Data.Text.Prettyprint.Doc
import Data.Data (Data, Typeable)

infixr 2 :->*:

data Kind
  = Star
  | Kind :->*: Kind
  deriving (Show, Eq, Data, Typeable)

instance Pretty Kind where
  pretty = rndr False where
    rndr p = \case 
      Star -> "*"
      k1 :->*: k2 -> parensIf $ rndr True k1 <+> "->" <+> rndr False k2
      where
        parensIf = if p then parens else id
