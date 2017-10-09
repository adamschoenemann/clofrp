{-# LANGUAGE DeriveFunctor #-}

module CloTT.Parser.Expr where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.Annotated  as A
import qualified CloTT.AST.Parsed as E
import qualified CloTT.AST.Prim   as P
import           CloTT.Parser.Lang
import qualified CloTT.Parser.Type as T
import           CloTT.AST.Name

type Expr = E.Expr SourcePos
type Pat  = E.Pat  SourcePos

nat :: Parser Expr
nat = ann <*> (E.Prim . P.Nat <$> natural)

bool :: Parser Expr
bool = ann <*> (E.Prim . P.Bool <$> b) where
  b =   reserved "True" *> pure True
    <|> reserved "False" *> pure False

tuple :: Parser Expr
tuple = ann <*> parens ((\e1 e2 -> E.Tuple e1 e2) <$> expr <* comma <*> expr)

lname :: Parser Name
lname = UName <$> lidentifier

tickabs :: Parser Expr
tickabs = do
  ps <- symbol "\\\\" *> many1 param
  bd <- reservedOp "->" *> expr
  pure $ foldr (\(A.A ann (nm, kappa)) acc -> A.A ann $ E.TickAbs nm kappa acc) bd ps
  where
    param = ann <*> parens ((,) <$> lname <*> (reservedOp ":" *> lname))
            

lam :: Parser Expr
lam = do
  ps <- symbol "\\" *> many1 param
  bd <- reservedOp "->" *> expr
  pure $ foldr (\(A.A ann nm, ty) acc -> A.A ann $ E.Lam nm ty acc) bd ps
  where
    param =  (\x -> (x, Nothing)) <$> (ann <*> lname)
         <|> parens ((,) <$> (ann <*> lname)
             <*> (optionMaybe $ reservedOp ":" *> T.typep))

var :: Parser Expr
var = ann <*> (E.Var . UName <$> identifier)

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


pat :: Parser Pat
pat = ann <*> p where
  p = (bind <|> match <|> parens p) 
  bind  = E.Bind . UName <$> lidentifier
  match = E.Match <$> (UName <$> uidentifier) <*> many (ann <*> pat')
  pat'  =  E.Match <$> (UName <$> uidentifier) <*> pure [] 
        <|> E.Bind . UName <$> lidentifier
        <|> parens (E.Match <$> (UName <$> uidentifier) <*> many pat)

atom :: Parser Expr
atom =   nat
     <|> bool
     <|> try tuple
     <|> var
     <|> anno
     <|> casep
     <|> parens expr

expr :: Parser Expr
expr = try tickabs <|> lam <|> buildExpressionParser table atom where
  table = 
    [ [Infix spacef AssocLeft]
    ]
  spacef :: Parser (Expr -> Expr -> Expr)
  spacef =
    ws *> notFollowedBy (choice . map reservedOp $ opNames) *> app
       <?> "space application"
  app :: Parser (Expr -> Expr -> Expr)
  app = fn <$> getPosition where
    fn p (A.A p1 e1) e2 = A.A p $ E.App (A.A p1 e1) e2

parseExpr :: String -> Either ParseError Expr
parseExpr = parse expr "parseExpr"