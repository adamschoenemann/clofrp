
module CloFRP.TestUtils where

import Test.Tasty.Hspec
import Data.Text (Text, unpack)
import Text.Parsec
import Text.Parsec.Pos
import Data.String (fromString)

import CloFRP.Pretty
import CloFRP.Parser.Prog (parseProg)
import CloFRP.Parser.Expr (parseExpr)
import CloFRP.AST
import qualified CloFRP.Eval.Value as V

instance Pretty (SourcePos) where
  pretty = fromString . show


success :: Expectation
success = pure ()

failure :: String -> Expectation
failure = expectationFailure

pprog :: Text -> Either ParseError (Prog SourcePos)
pprog = parseProg . unpack

pexpr :: Text -> Either ParseError (Expr SourcePos)
pexpr = parseExpr . unpack

pexprua :: Text -> Either ParseError (Expr ())
pexprua txt = case parseExpr . unpack $ txt of
  Right e  -> Right (unann e)
  Left err -> Left err
