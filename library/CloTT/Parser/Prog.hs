module CloTT.Parser.Prog where

import Text.Parsec.Pos
import Text.Parsec.String
import Text.Parsec (parse, ParseError)
import Text.Parsec.Combinator (eof)

import qualified CloTT.AST as E
import qualified CloTT.Parser.Decl as P
import qualified CloTT.Parser.Lang as P

type Prog = E.Prog SourcePos

prog :: Parser Prog
prog = E.Prog <$> P.decls


parseProg :: String -> Either ParseError Prog
parseProg p = parse (P.ws *> prog <* eof) "parseProg" p