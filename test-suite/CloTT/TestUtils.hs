
module CloTT.TestUtils where

import Test.Tasty.Hspec
import Data.Text (Text, unpack)
import Text.Parsec
import CloTT.Parser.Prog (parseProg)
import CloTT.Parser.Expr (parseExpr)
import CloTT.AST
import qualified CloTT.Eval.Value as V

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
