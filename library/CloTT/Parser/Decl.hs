module CloTT.Parser.Decl where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.AST.Parsed as E
import           CloTT.Parser.Lang
import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Expr as P
import           CloTT.AST.Name

type Decl = E.Decl SourcePos

decls :: Parser [Decl]
decls = many decl

decl :: Parser Decl
decl = datad <|> try fund <|> sigd

fund :: Parser Decl
fund = ann <*> p <* reservedOp "." where 
  p = E.FunD <$> (UName <$> identifier) <*> (reservedOp "=" *> P.expr)

datad :: Parser Decl
datad = ann <*> p where
  p = do 
    nm <- E.UName <$> (reserved "data" *> identifier)
    vars <- many identifier
    let kind = foldr (\_ b -> E.Star E.:->*:b ) E.Star vars
    let bound = map UName vars
    constrs <- (reservedOp "=" *> (constr `sepBy` symbol "|")) <* reservedOp "."
    pure $ E.DataD nm kind bound constrs

sigd :: Parser Decl
sigd = ann <*> p <* reservedOp "." where
  p = E.SigD <$> (UName <$> identifier) <*> (reservedOp ":" *> P.typep)

constr :: Parser (E.Constr SourcePos)
constr = ann <*> (E.Constr <$> (UName <$> identifier) <*> params) where
  -- to achieve the "space-separation" of constructor params, we have to do this instead of
  -- just `many P.typep`
  params = many (ann <*> (E.TFree . UName <$> identifier) <|> parens P.typep)


