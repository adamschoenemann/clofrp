module CloTT.Parser.Decl where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.Annotated  as A
import qualified CloTT.AST.Parsed as E
import           CloTT.Parser.Lang
import qualified CloTT.Parser.Type as T
import           CloTT.AST.Name

-- type Decl = E.Decl SourcePos
type Decl = (String,String)

data ParsedDecl a 
  = Fun Name (E.Expr a)
  | DataDecl Name E.Kind [E.Constr a]
  deriving (Show, Eq)

decls = many decl

-- decl :: Parser Decl
decl = datadecl <|> fundef 

fundef = undefined

datadecl :: Parser (E.Decl SourcePos)
datadecl = ann <*> p where
  p = E.DataDecl <$> 
        (E.UName <$> (reserved "data" *> identifier)) <*>
        (foldr (\a b -> E.Star E.:->*:b ) E.Star <$> many identifier) <*> 
        (reservedOp "=" *> (constr `sepBy` symbol "|")) <*
        reservedOp "."

constr :: Parser (E.Constr SourcePos)
constr = ann <*> (E.Constr <$> (UName <$> identifier) <*> many T.typep)

