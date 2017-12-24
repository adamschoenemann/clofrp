module CloFRP.Parser.Decl where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloFRP.AST as E
import           CloFRP.Parser.Lang
import qualified CloFRP.Parser.Type as P
import qualified CloFRP.Parser.Expr as P
import qualified CloFRP.Parser.Synonym as P
import           CloFRP.AST.Name

type Decl = E.Decl SourcePos

decls :: Parser [Decl]
decls = many decl

-- using monadic parser style here is a bit annoying, but
-- it improves the parser error messages significantly
decl :: Parser Decl
decl = datad <|> synonym <|> p where
  p = do
    nm <- lidentifier
    op <- (oneOf [':', '=']) <* ws
    let p' = case op of
              '=' -> E.FunD (UName nm) <$> P.expr
              ':' -> E.SigD (UName nm) <$> P.typep
              _   -> error "the impossible happened"
    ann <*> p' <* reservedOp "."
  synonym = ann <*> (E.SynonymD <$> P.synonym)

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
    bound <- many P.boundp
    constrs <- (reservedOp "=" *> (constr `sepBy` symbol "|")) 
    derivs <- option [] $ reserved "deriving" *> ((:[]) <$> uidentifier <|> parens (many1 uidentifier))
    _ <- reservedOp "."
    pure $ E.DataD (E.Datatype nm bound constrs derivs)


constr :: Parser (E.Constr SourcePos)
constr = ann <*> (E.Constr <$> (UName <$> uidentifier) <*> args) where
  -- to achieve the "space-separation" of constructor args, we have to do this instead of
  -- just `many P.typep`
  args = many ((P.tvar <|> P.free) <|> try P.ttuple <|> parens P.typep)


