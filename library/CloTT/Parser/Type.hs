{-# LANGUAGE DataKinds #-}

module CloTT.Parser.Type where

import Text.Parsec.Pos
import Text.Parsec
import Data.Foldable (foldrM)

import qualified CloTT.Annotated  as A
import qualified CloTT.AST.Parsed as E
import           CloTT.Parser.Lang
import           CloTT.AST.Name

type Type = E.Type SourcePos E.Poly

free :: Parser Type
free = ann <*> (E.TFree . UName <$> uidentifier) <?> "free"

tvar :: Parser Type
tvar = ann <*> (E.TVar . UName <$> lidentifier) <?> "tvar"

arr :: Parser (Type -> Type -> Type)
arr = pure (\p a b -> A.A p $ a E.:->: b) <*> getPosition <?> "arr"

forAll :: Parser Type
forAll = p <?> "forall" where
  p = do
    nms <- reserved "forall" *> (map UName <$> many1 lidentifier) <* reservedOp "."
    ty <- typep
    foldrM fn ty nms
  fn nm t = (\p -> A.A p $ E.Forall nm t) <$> getPosition

clocks :: Parser Type
clocks = p <?> "clocks" where
  p = do
    nms <- reserved "clocks" *> (map UName <$> many1 lidentifier) <* reservedOp "."
    ty <- typep
    foldrM fn ty nms
  fn nm t = (\p -> A.A p $ E.Clock nm t) <$> getPosition

recTy :: Parser Type
recTy = (ann <*> p) <?> "Fix" where
  p = E.RecTy <$> (reserved "Fix" *> typeexpr)

typeexpr :: Parser Type
typeexpr = tvar <|> free <|> forAll <|> clocks <|> recTy <|> parens typep

typep :: Parser Type
typep = buildExpressionParser table typeexpr where
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
