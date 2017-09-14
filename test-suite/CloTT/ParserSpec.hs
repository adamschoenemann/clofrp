{-# LANGUAGE OverloadedStrings #-}

module CloTT.ParserSpec where

import Test.Tasty.Hspec
import Text.Parsec
import Data.Either (isLeft)

import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Decl as P
import qualified CloTT.AST.Parsed  as E
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))

import CloTT.TestUtils

parserSpec :: Spec
parserSpec = do
  it "parses natural numbers" $ do
    do let Right e = parse P.expr "" "10"
       E.unannE e `shouldBe` E.nat 10
    do let r = parse P.expr "" "-1"
       r `shouldSatisfy` isLeft
  
  it "parses booleans (true)" $ do
    let Right e = E.unannE <$> parse P.expr "" "True"
    e `shouldBe` E.true
  
  it "parses booleans (false)" $ do
    let Right e = E.unannE <$> parse P.expr "" "False"
    e `shouldBe` E.false
  
  it "parses tuples" $ do
    do let Right e = E.unannE <$> parse P.expr "" "(10, False)"
       e `shouldBe` E.nat 10 @* E.false
    do let Right e = E.unannE <$> parse P.expr "" "(True, 5)"
       e `shouldBe` E.true @* E.nat 5
  
  it "parses vars" $ do
    do let Right e = E.unannE <$> parse P.expr "" "x"
       e `shouldBe` "x"
    do let Right e = E.unannE <$> parse P.expr "" "truefalse"
       e `shouldBe` "truefalse"
  
  it "parses lambdas" $ do
    do let Right e = E.unannE <$> parse P.expr "" "\\x -> x"
       e `shouldBe` "x" @-> "x"
    do let Right e = E.unannE <$> parse P.expr "" "\\x -> (x, True)"
       e `shouldBe` "x" @-> "x" @* E.true
    do let Right e = E.unannE <$> parse P.expr "" "\\x -> \\y -> x"
       e `shouldBe` "x" @-> "y" @-> "x"
    case E.unannE <$> parse P.expr "" "\\(x:Bool) -> \\(y:Int) -> x" of
      Left e -> failure $ show e 
      Right e -> e `shouldBe` ("x", "Bool") @:-> ("y", "Int") @:-> "x"
  
  it "parses application" $ do
    do let Right e = E.unannE <$> parse P.expr "" "e1 e2"
       e `shouldBe` "e1" @@ "e2"
    do let Right e = E.unannE <$> parse P.expr "" "e1 e2 e3"
       e `shouldBe` ("e1" @@ "e2" @@ "e3")
  
  it "parses annotations" $ do
    case E.unannE <$> parse P.expr "" "the (Bool -> Int) (\\x -> 10)" of
      Left e -> failure $ show e
      Right e -> e `shouldBe` ("x" @-> E.nat 10) @:: ("Bool" @->: "Int")
    case E.unannE <$> parse P.expr "" "the (Bool -> Int -> Int) (\\x -> \\y -> 10)" of
      Left e -> failure $ show e
      Right e -> e `shouldBe` ("x" @-> "y" @-> E.nat 10) @:: ("Bool" @->: "Int" @->: "Int")
  
  it "parses case statements" $ do
    case E.unannE <$> parse P.expr "" "case x of | y -> y" of
      Right e -> e `shouldBe` E.caseof "x" [("y", "y")]
      Left e -> failure $ show e
    case E.unannE <$> parse P.expr "" "case x of | Tuple a b -> 10 | y -> y" of
      Right e -> e `shouldBe` E.caseof "x" [(E.match "Tuple" ["a", "b"], E.nat 10), ("y", "y")]
      Left e -> failure $ show e
    case E.unannE <$> parse P.expr "" "case x of | Tuple (Cons x y) b -> 10 | y -> y" of
      Right e -> e `shouldBe` E.caseof "x" [(E.match "Tuple" [E.match "Cons" ["x", "y"], "b"], E.nat 10), ("y", "y")]
      Left e -> failure $ show e
    case E.unannE <$> parse P.expr "" "case n of | Z -> n | S n' -> n'" of
      Right e -> e `shouldBe` E.caseof "n" [(E.match "Z" [], "n"), (E.match "S" ["n'"], "n'")]
      Left e -> failure $ show e
  
  it "parses compound expressions" $ 
    do let Right e = E.unannE <$> parse P.expr "" "\\x -> (\\y -> x y, y (True,x))"
       e `shouldBe` "x" @-> ("y" @-> "x" @@ "y") @* "y" @@ (E.true @* "x")
  
  it "parses simple types" $ do
    do let Right e = E.unannT <$> parse P.typep "" "x"
       e `shouldBe` "x"
    do let Right e = E.unannT <$> parse P.typep "" "typez"
       e `shouldBe` "typez"
  
  it "parses arrow types" $ do
    do let Right e = E.unannT <$> parse P.typep "" "a -> b"
       e `shouldBe` "a" @->: "b"
    do let Right e = E.unannT <$> parse P.typep "" "a -> b -> c"
       e `shouldBe` "a" @->: "b" @->: "c"
    do let Right e = E.unannT <$> parse P.typep "" "(a -> b) -> c"
       e `shouldBe` ("a" @->: "b") @->: "c"

  it "parses foralls" $ do
    do let Right e = E.unannT <$> parse P.typep "" "forall a. a"
       e `shouldBe` E.forAll ["a"] "a"
    do let Right e = E.unannT <$> parse P.typep "" "forall a. a -> Int"
       e `shouldBe` E.forAll ["a"] ("a" @->: "Int")
    do let Right e = E.unannT <$> parse P.typep "" "forall a b. (a -> b) -> (b -> a) -> Iso a b"
       e `shouldBe` E.forAll ["a", "b"] (("a" @->: "b") @->: ("b" @->: "a") @->: "Iso" @@: "a" @@: "b")
    do let Right e = E.unannT <$> parse P.typep "" "forall a. (forall b. a -> b) -> b"
       e `shouldBe` E.forAll ["a"] ((E.forAll ["b"] $ "a" @->: "b") @->: "b")
    do let Right e = E.unannT <$> parse P.typep "" "forall a. forall b. a -> b -> b"
       e `shouldBe` E.forAll ["a"] (E.forAll ["b"] $ "a" @->: "b" @->: "b")

declSpec :: Spec
declSpec = do
  it "parses data type decls" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "data Foo = ."
       decl `shouldBe` E.datad "Foo" Star [] []
    do let Right decl = E.unannD <$> parse P.decl "" "data Foo a = ."
       decl `shouldBe` E.datad "Foo" (Star :->*: Star) ["a"] []
    do let Right decl = E.unannD <$> parse P.decl "" "data Foo a b = ."
       decl `shouldBe` E.datad "Foo" (Star :->*: Star :->*: Star) ["a", "b"] []
    do let Right decl = E.unannD <$> parse P.decl "" "data Unit = MkUnit."
       decl `shouldBe` E.datad "Unit" Star [] [E.constr "MkUnit" []]
    do let Right decl = E.unannD <$> parse P.decl "" "data Bool = True | False."
       decl `shouldBe` E.datad "Bool" Star [] [E.constr "True" [], E.constr "False" []]
    do let Right decl = E.unannD <$> parse P.decl "" "data Maybe a = Nothing | Just a."
       decl `shouldBe` E.datad "Maybe" (Star :->*: Star) ["a"] [E.constr "Nothing" [], E.constr "Just" ["a"]]
    do let Right decl = E.unannD <$> parse P.decl "" "data List a = Nil | Cons (List a)."
       decl `shouldBe` E.datad "List" (Star :->*: Star) ["a"] [E.constr "Nil" [], E.constr "Cons" ["List" @@: "a"]]
    do let Right decl = E.unannD <$> parse P.decl "" "data Tree a = Leaf | Branch a (Tree a) (Tree a)."
       E.unannD decl `shouldBe`
          E.datad "Tree" (Star :->*: Star) ["a"]
                          [ E.constr "Leaf" []
                          , E.constr "Branch" ["a", "Tree" @@: "a", "Tree" @@: "a"]
                          ]

  it "parses function declarations" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "id = \\x -> x."
       decl `shouldBe` E.fund "id" ("x" @-> "x")

  it "parses type signatures" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "id : a -> a."
       decl `shouldBe` E.sigd "id" ("a" @->: "a")
    do let Right decl = E.unannD <$> parse P.decl "" "map : (a -> b) -> f a -> f b."
       decl `shouldBe` E.sigd "map" (("a" @->: "b") @->: "f" @@: "a" @->: "f" @@: "b")