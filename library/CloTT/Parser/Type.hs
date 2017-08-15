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
    [ [Infix spacef AssocLeft]
    , [binary' "->" arr AssocRight]
    ]
  spacef :: Parser (Type -> Type -> Type)
  spacef =
    ws *> notFollowedBy (choice . map reservedOp $ opNames) *> app
       <?> "space application"
  app :: Parser (Type -> Type -> Type)
  app = fn <$> getPosition where
    fn p t1 t2 = A.A p $ E.TApp t1 t2
