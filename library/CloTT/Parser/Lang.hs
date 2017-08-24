{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-|
Module      : CloTT.Parser.Lang
Description : Language definition for CloTT programs
-}
module CloTT.Parser.Lang (
    module CloTT.Parser.Lang
  , Operator(..)
  , Assoc(..)
  , Parser
  , buildExpressionParser
) where

import qualified CloTT.Annotated as A

import Text.Parsec.String
import Text.Parsec
import Text.Parsec.Expr
import Data.Char (isUpper, isLower)
import qualified Text.Parsec.Token as Tok

-- instance Pretty SourcePos where
--   ppr n sp =
--     text "line" <+> int (sourceLine sp) <+> "column" <+> int (sourceColumn sp)

opNames :: [String]
opNames    = [ "+", "-", "*", "/", "=", "==", "&&", "||"
             , "<", ">", "<=", ">=", "\\", "->", "|", ":", "."
             ]

languageDef :: Tok.LanguageDef ()
languageDef = Tok.LanguageDef
  { Tok.commentStart    = "{-"
  , Tok.commentEnd      = "-}"
  , Tok.commentLine     = "--"
  , Tok.nestedComments  = True
  , Tok.identStart      = letter
  , Tok.identLetter     = alphaNum <|> oneOf "_'"
  , Tok.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Tok.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Tok.reservedNames   = [ "if"
                          , "then"
                          , "else"
                          , "cons"
                          , "let"
                          , "in"
                          , "delay"
                          , "stable"
                          , "promote"
                          , "fst"
                          , "snd"
                          , "promote"
                          , "inl"
                          , "inr"
                          , "case"
                          , "of"
                          , "out"
                          , "into"
                          , "alloc"
                          , "fix"
                          , "mu"
                          , "()"
                          , "undefined"
                          , "import"
                          , "the"
                          , "data"
                          , "forall"
                          ]
  , Tok.reservedOpNames = opNames
  , Tok.caseSensitive   = True
  }

binary'  name fun assoc = Infix   (reservedOp name >> fun) assoc
prefix'  name fun       = Prefix  (reservedOp name >> fun)
postfix' name fun       = Postfix (reservedOp name >> fun)

binary  name fun assoc = Infix   (reservedOp name >> return fun) assoc
prefix  name fun       = Prefix  (reservedOp name >> return fun)
postfix name fun       = Postfix (reservedOp name >> return fun)

lexer      = Tok.makeTokenParser languageDef
identifier = Tok.identifier lexer -- parses an identifier

satisfies predicate err p = do
  r <- try p
  if (predicate r)
    then pure r
    else unexpected (err r)

inIdent = many $ alphaNum <|> oneOf ['\'', '_']
uidentifier = lexeme $ (:) <$> upper <*> inIdent
lidentifier = lexeme $ (:) <$> lower <*> inIdent

-- uidentifier = satisfies (isUpper . head) (\ident -> ident ++ " must start with an upper-case character") identifier
-- lidentifier = satisfies (isLower . head) (\ident -> ident ++ " must start with a lower-case character")  identifier

reserved   = Tok.reserved   lexer -- parses a reserved name
reservedOp = Tok.reservedOp lexer -- parses an operator
parens     = Tok.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Tok.integer    lexer -- parses an integer
natural    = Tok.natural    lexer
ws         = Tok.whiteSpace lexer -- parses whitespace
comma      = Tok.comma lexer
symbol     = Tok.symbol lexer
lexeme     = Tok.lexeme lexer

ann :: Parser (t -> A.Annotated SourcePos t)
ann = A.A <$> getPosition