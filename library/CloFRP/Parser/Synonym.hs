
module CloFRP.Parser.Synonym where

import Text.Parsec.Pos
import Text.Parsec

import qualified CloFRP.AST as E
import           CloFRP.Parser.Lang
import qualified CloFRP.Parser.Type as P
import           CloFRP.AST.Name

type Synonym = E.Synonym SourcePos

synonym :: Parser Synonym
synonym = p where
  p = E.Synonym <$> (reserved "type" *> (UName <$> uidentifier))
              <*> (many P.boundp)
              <*> (reservedOp "=" *> P.typep <* reservedOp ".")
