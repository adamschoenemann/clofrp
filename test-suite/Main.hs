-- Tasty makes it easy to test your code. It is a test framework that can
-- combine many different types of tests into one suite. See its website for
-- help: <http://documentup.com/feuerbach/tasty>.
import qualified Test.Tasty
-- Hspec is one of the providers for Tasty. It provides a nice syntax for
-- writing tests. Its website has more info: <https://hspec.github.io>.
import Test.Tasty.Hspec

import Text.Parsec

import qualified CloTT.Parser.Expr as P
import qualified CloTT.AST.Parsed  as E
import qualified CloTT.Annotated   as A

main :: IO ()
main = do
    test <- testSpec "clott" spec
    Test.Tasty.defaultMain test

spec :: Spec
spec = parallel $ do
    it "is trivially true" $ do
        True `shouldBe` True
    it "parses natural numbers" $ do
        let Right e = parse P.nat "" "10"
        E.unann e `shouldBe` A.A () (E.Prim $ E.Nat 10)
        True `shouldBe` True

