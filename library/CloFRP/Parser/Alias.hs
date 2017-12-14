
module CloFRP.Parser.Alias where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloFRP.AST as E
import           CloFRP.Parser.Lang
import qualified CloFRP.Parser.Type as P
import           CloFRP.AST.Name

type Alias = E.Alias SourcePos

alias :: Parser Alias
alias = p where
  p = E.Alias <$> (reserved "type" *> (UName <$> uidentifier))
              <*> (many P.boundp)
              <*> (reservedOp "=" *> P.typep <* reservedOp ".")
