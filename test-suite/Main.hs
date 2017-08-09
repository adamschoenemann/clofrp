{-# LANGUAGE OverloadedStrings #-}

-- Tasty makes it easy to test your code. It is a test framework that can
-- combine many different types of tests into one suite. See its website for
-- help: <http://documentup.com/feuerbach/tasty>.
import qualified Test.Tasty
-- Hspec is one of the providers for Tasty. It provides a nice syntax for
-- writing tests. Its website has more info: <https://hspec.github.io>.
import Test.Tasty.Hspec

import Text.Parsec
import Data.Either (isLeft)

import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Type as P
import qualified CloTT.AST.Parsed  as E
import           CloTT.AST.Parsed (LamCalc(..))
import qualified CloTT.Annotated   as A

main :: IO ()
main = do
  test <- testSpec "clott" spec
  Test.Tasty.defaultMain test

spec :: Spec
spec = do
  it "is trivially true" $ do
    True `shouldBe` True
  it "parses natural numbers" $ do
    do let Right e = parse P.expr "" "10"
       E.unann e `shouldBe` E.nat 10
    do let r = parse P.expr "" "-1"
       r `shouldSatisfy` isLeft
  it "parses booleans (true)" $ do
    let Right e = E.unann <$> parse P.expr "" "True"
    e `shouldBe` E.true
  it "parses booleans (false)" $ do
    let Right e = E.unann <$> parse P.expr "" "False"
    e `shouldBe` E.false
  it "parses tuples" $ do
    do let Right e = E.unann <$> parse P.expr "" "(10, False)"
       e `shouldBe` E.nat 10 @* E.false
    do let Right e = E.unann <$> parse P.expr "" "(True, 5)"
       e `shouldBe` E.true @* E.nat 5
  it "parses vars" $ do
    do let Right e = E.unann <$> parse P.expr "" "x"
       e `shouldBe` "x"
    do let Right e = E.unann <$> parse P.expr "" "truefalse"
       e `shouldBe` "truefalse"
  it "parses lambdas" $ do
    do let Right e = E.unann <$> parse P.lam "" "\\x -> x"
       e `shouldBe` "x" @-> "x"
    do let Right e = E.unann <$> parse P.lam "" "\\x -> (x, True)"
       e `shouldBe` "x" @-> "x" @* E.true
    do let Right e = E.unann <$> parse P.lam "" "\\x -> \\y -> x"
       e `shouldBe` "x" @-> "y" @-> "x"
  it "parses simple types" $ do
    do let Right e = E.unannT <$> parse P.typep "" "x"
       e `shouldBe` "x"
    do let Right e = E.unannT <$> parse P.typep "" "typez"
       e `shouldBe` "typez"
  it "parses arrow types" $ do
    do let Right e = E.unannT <$> parse P.typep "" "a -> b"
       e `shouldBe` "a" E.@->: "b"
    do let Right e = E.unannT <$> parse P.typep "" "a -> b -> c"
       e `shouldBe` "a" E.@->: "b" E.@->: "c"
    do let Right e = E.unannT <$> parse P.typep "" "(a -> b) -> c"
       e `shouldBe` ("a" E.@->: "b") E.@->: "c"


