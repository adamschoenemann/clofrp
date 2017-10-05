
module CloTT.Parser.Alias where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloTT.AST.Parsed as E
import           CloTT.Parser.Lang
import qualified CloTT.Parser.Type as P
import           CloTT.AST.Name

type Alias = E.Alias SourcePos

alias :: Parser Alias
alias = p where
  p = E.Alias <$> (reserved "type" *> (UName <$> uidentifier))
              <*> (map UName <$> many lidentifier)
              <*> (reservedOp "=" *> P.typep <* reservedOp ".")
