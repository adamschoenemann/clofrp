{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}

module CloTT.Parser.Expr where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.Annotated  as A
import qualified CloTT.AST.Parsed as E
import qualified CloTT.AST.Prim   as P
import           CloTT.Parser.Lang
import qualified CloTT.Parser.Type as T
import           CloTT.AST.Name
import           CloTT.Pretty ((<+>), pretty)

type Expr = E.Expr SourcePos
type Pat  = E.Pat  SourcePos

nat :: Parser Expr
nat = ann <*> (E.Prim . P.Nat <$> natural)

tuple :: Parser Expr
tuple = ann <*> (E.Tuple <$> parens (expr `sepBy2` comma))

lname :: Parser Name
lname = UName <$> lidentifier

clockabs :: Parser Expr
clockabs = do
  ps <- symbol "/\\" *> many1 param
  bd <- reservedOp "->" *> expr
  pure $ foldr (\(A.A a kappa) acc -> A.A a $ E.ClockAbs kappa acc) bd ps
  where
    param = ann <*> lname

tickabs :: Parser Expr
tickabs = do
  ps <- symbol "\\\\" *> many1 param
  bd <- reservedOp "->" *> expr
  pure $ foldr (\(A.A a (nm, kappa)) acc -> A.A a $ E.TickAbs nm kappa acc) bd ps
  where
    param = ann <*> parens ((,) <$> lname <*> (reservedOp ":" *> lname))
            
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
tickvar = ann <*> (E.TickVar <$> braces lname)

clockvar :: Parser Expr
clockvar = ann <*> (E.ClockVar <$> brackets lname)

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
     <|> reserved "primRec" *> (ann <*> pure (E.Prim E.PrimRec))
     <|> letp
     <|> var
     <|> tickvar
     <|> clockvar
     <|> anno
     <|> casep
     <|> parens expr

expr :: Parser Expr
expr = clockabs <|> try tickabs <|> lam <|> buildExpressionParser table atom where
  table = 
    [ [Infix spacef AssocLeft, Postfix tanno]
    ]

  spacef :: Parser (Expr -> Expr -> Expr)
  spacef =
    ws *> notFollowedBy (choice . map reservedOp $ opNames) *> app
       <?> "space application"
  
  tanno :: Parser (Expr -> Expr)
  tanno = do
    p <- getPosition
    t <- reservedOp ":" *> T.typep
    pure (\e -> A.A p $ E.Ann e t)

  -- clockf :: Parser (Expr -> Expr)
  -- clockf = do 
  --   p <- getPosition
  --   -- nasty hack to make it behave "infixl" ish 
  --   nms <- many1 (ann <*> (symbol "[" *> lname <* symbol "]"))
  --   pure (\e -> foldl (\acc (A.A ann nm) -> A.A ann $ E.ClockApp acc nm) e nms)

  app :: Parser (Expr -> Expr -> Expr)
  app = fn <$> getPosition where
    fn p e1 e2 = A.A p $ E.App e1 e2

parseExpr :: String -> Either ParseError Expr
parseExpr = parse expr "parseExpr"