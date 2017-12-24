{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}

module CloFRP.Parser.Expr where

import Text.Parsec.Pos
import Text.Parsec
import Data.List (foldl')

import qualified CloFRP.Annotated  as A
import qualified CloFRP.AST as E
import qualified CloFRP.AST.Prim   as P
import           CloFRP.Parser.Lang
import qualified CloFRP.Parser.Type as T
import           CloFRP.AST.Name

type Expr = E.Expr SourcePos
type Pat  = E.Pat  SourcePos

nat :: Parser Expr
nat = ann <*> (E.Prim . P.Integer <$> natural)

tuple :: Parser Expr
tuple = ann <*> (E.Tuple <$> parens (expr `sepBy2` comma))

lname :: Parser Name
lname = UName <$> lidentifier

name :: Parser Name
name = UName <$> identifier

tickabs :: Parser Expr
tickabs = do
  ps <- symbol "\\\\" *> many1 param
  bd <- reservedOp "->" *> expr
  pure $ foldr (\(A.A a (nm, kappa)) acc -> A.A a $ E.TickAbs nm kappa acc) bd ps
  where
    param = ann <*> parens ((,) <$> lname <*> (reservedOp ":" *> name))
            
letp :: Parser Expr
letp = ann <*> p where 
  p = E.Let <$> (reserved "let" *> pat <* reservedOp "=") <*> (expr <* reserved "in") <*> expr

lam :: Parser Expr
lam = do
  ps <- symbol "\\" *> many1 param
  bd <- reservedOp "->" *> expr
  pure $ foldr (\(A.A a nm, ty) acc -> A.A a $ E.Lam nm ty acc) bd ps
  where
    param =  (\x -> (x, Nothing)) <$> (ann <*> lname)
         <|> parens ((,) <$> (ann <*> lname)
             <*> (optionMaybe $ reservedOp ":" *> T.typep))

var :: Parser Expr
var = ann <*> (E.Var . UName <$> identifier)

tickvar :: Parser Expr
tickvar = ann <*> (E.TickVar <$> brackets lname)

anno :: Parser Expr
anno = ann <*> ((\t e -> E.Ann e t) <$> (reserved "the" *> parens T.typep) <*> expr)

casep :: Parser Expr
casep = do
  _ <- reserved "case"
  scrutinee <- expr
  _ <- reserved "of"
  _ <- reservedOp "|"
  ann <*> (E.Case scrutinee <$> matchp `sepBy` (reservedOp "|"))
  where
    matchp = (,) <$> (pat <* reservedOp "->") <*> expr

fmapp :: Parser Expr
fmapp = ann <*> p where 
  p = E.Fmap <$> (reserved "fmap" *> braces (T.typep))

primRecP :: Parser Expr
primRecP = ann <*> p where 
  p = E.PrimRec <$> (reserved "primRec" *> braces (T.typep))


-- a bit annoying with all this copy-paste but meh
pat :: Parser Pat
pat = ann <*> p where
  p = (bind <|> match <|> try ptuple <|> parens p) 
  bind    = E.Bind . UName <$> lidentifier
  match   = E.Match <$> (UName <$> uidentifier) <*> many (ann <*> pat')
  ptuple  = parens (E.PTuple <$> pat `sepBy2` comma)
  pat'  =  E.Match <$> (UName <$> uidentifier) <*> pure [] 
        <|> E.Bind . UName <$> lidentifier
        <|> try (parens (E.PTuple <$> pat `sepBy2` comma))
        <|> parens (E.Match <$> (UName <$> uidentifier) <*> many pat)

atom :: Parser Expr
atom =   nat
     <|> try tuple
     <|> reserved "fold" *> (ann <*> pure (E.Prim E.Fold))
     <|> reserved "unfold" *> (ann <*> pure (E.Prim E.Unfold))
     <|> reserved "[<>]" *> (ann <*> pure (E.Prim E.Tick))
     <|> reserved "fix" *> (ann <*> pure (E.Prim E.Fix))
     <|> reserved "undefined" *> (ann <*> pure (E.Prim E.Undefined))
     <|> primRecP 
     <|> fmapp
     <|> letp
     <|> var
     <|> tickvar
     <|> anno
     <|> casep
     <|> parens expr

expr :: Parser Expr
expr = try tickabs <|> lam <|> buildExpressionParser table atom where
  table = 
    [ [Infix spacef AssocLeft, Postfix typeapp]
    , [binary' "+" (binOp "+") AssocLeft]
    , [binary' "<" (binOp "<") AssocLeft]
    , [Postfix tanno]
    ]
  
  binOp nm = do
    p <- getPosition
    pure (\e1 -> A.A p . E.BinOp nm e1)

  spacef :: Parser (Expr -> Expr -> Expr)
  spacef =
    ws *> notFollowedBy (choice . map reservedOp $ opNames) *> app
       <?> "space application"
  
  tanno :: Parser (Expr -> Expr)
  tanno = do
    p <- getPosition
    t <- reservedOp ":" *> T.typep
    pure (\e -> A.A p $ E.Ann e t)

  typeapp :: Parser (Expr -> Expr)
  typeapp = do 
    p <- getPosition
    -- nasty hack to make it behave "infixl" ish 
    ts <- many1 (ann <*> braces T.typep)
    pure (\e -> foldl' (\acc (A.A a t) -> A.A a $ E.TypeApp acc t) e ts)

  app :: Parser (Expr -> Expr -> Expr)
  app = fn <$> getPosition where
    fn p e1 e2 = A.A p $ E.App e1 e2

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (ws *> expr <* eof) "parseExpr"