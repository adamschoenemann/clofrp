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
      Right e -> e `shouldBe` ("x", E.free "Bool") @:-> ("y", E.free "Int") @:-> "x"

  it "parses multi-param lambdas" $ do
    do let Right e = E.unannE <$> parse P.expr "" "\\x y z -> x"
       e `shouldBe` "x" @-> "y" @-> "z" @-> "x"
    do let Right e = E.unannE <$> parse P.expr "" "\\x (y:Int) (z:Bool) -> x"
       e `shouldBe` "x" @-> ("y", "Int") @:-> ("z", "Bool") @:-> "x"
  
  it "parses application" $ do
    do let Right e = E.unannE <$> parse P.expr "" "e1 e2"
       e `shouldBe` "e1" @@ "e2"
    do let Right e = E.unannE <$> parse P.expr "" "e1 e2 e3"
       e `shouldBe` ("e1" @@ "e2" @@ "e3")
    do let Right e = E.unannE <$> parse P.expr "" "e1 (e2 e3) e4 (\\x -> x) e5)"
       e `shouldBe` ("e1" @@ ("e2" @@ "e3") @@ "e4" @@ ("x" @-> "x") @@ "e5")

  it "success: clock application (1)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "e1 [k]"
       e `shouldBe` "e1" `E.capp` "k"
  it "success: clock application (2)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "(e1 [k1]) [k2]"
       e `shouldBe` "e1" `E.capp` "k1" `E.capp` "k2"
  it "success: clock application (3)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "e1 [k1] [k2]"
       e `shouldBe` "e1" `E.capp` "k1" `E.capp` "k2"
  it "success: clock application (4)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "(e1 [k1] [k2]) e2"
       e `shouldBe` ("e1" `E.capp` "k1" `E.capp` "k2") @@ "e2"
  it "success: clock application (5)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "(e1 e2 [k2]) e2"
       e `shouldBe` ("e1" @@ "e2" `E.capp` "k2") @@ "e2"
  
  it "parses annotations" $ do
    case E.unannE <$> parse P.expr "" "the (Bool -> Int) (\\x -> 10)" of
      Left e -> failure $ show e
      Right e -> e `shouldBe` ("x" @-> E.nat 10) @:: (E.free "Bool" @->: E.free "Int")
    case E.unannE <$> parse P.expr "" "the (Bool -> Int -> Int) (\\x -> \\y -> 10)" of
      Left e -> failure $ show e
      Right e -> e `shouldBe` ("x" @-> "y" @-> E.nat 10) @:: (E.free "Bool" @->: E.free "Int" @->: E.free "Int")
  
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

  it "parses tick abstractions (1)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "\\\\(a : k) -> \\x -> x"
       e `shouldBe` (("a", "k") `E.tAbs` ("x" @-> "x"))

  it "parses tick abstractions (2)" $ do
    do let Right e = E.unannE <$> parse P.expr "" "\\\\(a : k) (b : k') -> \\x -> x"
       e `shouldBe` (("a", "k") `E.tAbs` (("b", "k'") `E.tAbs` ("x" @-> "x")))
  
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

  it "parses clock quantifiers" $ do
    do let Right e = E.unannT <$> parse P.typep "" "clocks a. a"
       e `shouldBe` E.clocks ["a"] "a"
    do let Right e = E.unannT <$> parse P.typep "" "clocks a. a -> Int"
       e `shouldBe` E.clocks ["a"] ("a" @->: "Int")
    do let Right e = E.unannT <$> parse P.typep "" "clocks a b. (a -> b) -> (b -> a) -> Iso a b"
       e `shouldBe` E.clocks ["a", "b"] (("a" @->: "b") @->: ("b" @->: "a") @->: "Iso" @@: "a" @@: "b")
    do let Right e = E.unannT <$> parse P.typep "" "clocks a. (clocks b. a -> b) -> b"
       e `shouldBe` E.clocks ["a"] ((E.clocks ["b"] $ "a" @->: "b") @->: "b")
    do let Right e = E.unannT <$> parse P.typep "" "clocks a. clocks b. a -> b -> b"
       e `shouldBe` E.clocks ["a"] (E.clocks ["b"] $ "a" @->: "b" @->: "b")
  
  it "parses typevars" $ do
    do let Right e = E.unannT <$> parse P.tvar "" "a"
       e `shouldBe` "a"
    do let Right e = map E.unannT <$> parse (many P.tvar) "" "a"
       e `shouldBe` ["a"] 
    do let Right e = map E.unannT <$> parse (many P.tvar) "" "a b"
       e `shouldBe` ["a", "b"] 

  it "parses free vars" $ do
    do let Right e = E.unannT <$> parse P.free "" "A"
       e `shouldBe` (E.free "A")
    do let Right e = map E.unannT <$> parse (many P.free) "" "A"
       e `shouldBe` [E.free "A"] 
    do let Right e = map E.unannT <$> parse (many P.free) "" "A B"
       e `shouldBe` [E.free "A", E.free "B"] 
  


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
       decl `shouldBe` E.datad "List" (Star :->*: Star) ["a"] [E.constr "Nil" [], E.constr "Cons" [E.free "List" @@: "a"]]
    do let Right decl = E.unannD <$> parse P.decl "" "data Tree a = Leaf | Branch a (Tree a) (Tree a)."
       E.unannD decl `shouldBe`
          E.datad "Tree" (Star :->*: Star) ["a"]
                          [ E.constr "Leaf" []
                          , E.constr "Branch" ["a", E.free "Tree" @@: "a", E.free "Tree" @@: "a"]
                          ]

  it "parses function declarations" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "id = \\x -> x."
       decl `shouldBe` E.fund "id" ("x" @-> "x")

  it "parses type signatures" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "id : a -> a."
       decl `shouldBe` E.sigd "id" ("a" @->: "a")
    do let Right decl = E.unannD <$> parse P.decl "" "map : (a -> b) -> f a -> f b."
       decl `shouldBe` E.sigd "map" (("a" @->: "b") @->: "f" @@: "a" @->: "f" @@: "b")

  it "parses type aliases" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "type Seconds = Int."
       decl `shouldBe` E.aliasd "Seconds" [] "Int"
    do let Right decl = E.unannD <$> parse P.decl "" "type Option a = Maybe a."
       decl `shouldBe` E.aliasd "Option" ["a"] ("Maybe" @@: "a")
    do let Right decl = E.unannD <$> parse P.decl "" "type Sum a b = Either a b."
       decl `shouldBe` E.aliasd "Sum" ["a", "b"] ("Either" @@: "a" @@: "b")
    do let Right decl = E.unannD <$> parse P.decl "" "type CList a = forall r. (a -> r -> r) -> r -> r."
       decl `shouldBe` E.aliasd "CList" ["a"] (E.forAll ["r"] $ ("a" @->: "r" @->: "r") @->: "r" @->: "r")