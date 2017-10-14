module CloTT.Parser.Prog where

import Text.Parsec.Pos
import Text.Parsec.String
import Text.Parsec (parse, ParseError)

import qualified CloTT.AST.Parsed as E
import qualified CloTT.Parser.Decl as P

type Prog = E.Prog SourcePos

prog :: Parser Prog
prog = E.Prog <$> P.decls


parseProg :: String -> Either ParseError Prog
parseProg p = parse prog "parseProg" p