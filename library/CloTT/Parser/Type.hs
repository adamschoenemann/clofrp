module CloTT.Parser.Type where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.Annotated  as A
import qualified CloTT.AST.Parsed as E
import           CloTT.Parser.Lang
import           CloTT.AST.Name

type Type = E.Type SourcePos

var :: Parser Type
var = ann <*> (E.TFree . UName <$> identifier)

arr :: Parser (Type -> Type -> Type)
arr = pure (\p a b -> A.A p $ a E.:->: b) <*> getPosition


typep :: Parser Type
typep = buildExpressionParser table (var <|> parens typep) where
  table = 
    [ [binary' "->" arr AssocRight]
    ]
