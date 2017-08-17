module CloTT.Parser.Prog where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.Parser.Decl as P

type Prog = E.Prog SourcePos

prog :: Parser Prog
prog = Prog <$> P.decls


