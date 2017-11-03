
module CloTT.TestUtils where

import Test.Tasty.Hspec
import Data.Text
import Text.Parsec
import CloTT.Parser.Prog (parseProg)
import CloTT.AST.Parsed

success :: Expectation
success = pure ()

failure :: String -> Expectation
failure = expectationFailure

pprog :: Text -> Either ParseError (Prog SourcePos)
pprog = parseProg . unpack