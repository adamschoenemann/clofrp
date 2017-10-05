module CloTT.Parser.Decl where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.AST.Parsed as E
import           CloTT.Parser.Lang
import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Alias as P
import           CloTT.AST.Name

type Decl = E.Decl SourcePos

decls :: Parser [Decl]
decls = many decl

-- using monadic parser style here is a bit annoying, but
-- it improves the parser error messages significantly
decl :: Parser Decl
decl = datad <|> alias <|> p where
  p = do
    nm <- lidentifier
    op <- (oneOf [':', '=']) <* ws
    let p' = case op of
              '=' -> E.FunD (UName nm) <$> P.expr
              ':' -> E.SigD (UName nm) <$> P.typep
              _   -> error "the impossible happened"
    ann <*> p' <* reservedOp "."
  alias = ann <*> (E.AliasD <$> P.alias)

-- sigd :: Parser Decl
-- sigd = ann <*> p <* reservedOp "." where
--   p = E.SigD <$> (UName <$> identifier) <*> (reservedOp ":" *> P.typep)

-- fund :: Parser Decl
-- fund = ann <*> p <* reservedOp "." where 
--   p = E.FunD <$> (UName <$> lidentifier) <*> (reservedOp "=" *> P.expr)

datad :: Parser Decl
datad = ann <*> p where
  p = do 
    nm <- E.UName <$> (reserved "data" *> uidentifier)
    vars <- many lidentifier
    let kind = foldr (\_ b -> E.Star E.:->*:b ) E.Star vars
    let bound = map UName vars
    constrs <- (reservedOp "=" *> (constr `sepBy` symbol "|")) <* reservedOp "."
    pure $ E.DataD nm kind bound constrs


constr :: Parser (E.Constr SourcePos)
constr = ann <*> (E.Constr <$> (UName <$> uidentifier) <*> args) where
  -- to achieve the "space-separation" of constructor args, we have to do this instead of
  -- just `many P.typep`
  args = many ((P.tvar <|> P.free) <|> parens P.typep)


