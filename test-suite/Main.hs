{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

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
import qualified CloTT.Parser.Decl as P
import qualified CloTT.AST.Parsed  as E
import           CloTT.AST.Parsed ((@->:), (@@:))
import           CloTT.AST.Parsed (LamCalc(..))
import qualified CloTT.Annotated   as A

import CloTT.QuasiQuoter

main :: IO ()
main = do
  test <- testSpec "parsing" spec
  quasi <- testSpec "quasi" quasiSpec
  tc <- testSpec "type checking" tcSpec
  decl <- testSpec "declarations" declSpec
  let group = Test.Tasty.testGroup "tests" [test, quasi, tc, decl]
  Test.Tasty.defaultMain group

spec :: Spec
spec = do
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
    do let Right e = E.unann <$> parse P.expr "" "\\x -> x"
       e `shouldBe` "x" @-> "x"
    do let Right e = E.unann <$> parse P.expr "" "\\x -> (x, True)"
       e `shouldBe` "x" @-> "x" @* E.true
    do let Right e = E.unann <$> parse P.expr "" "\\x -> \\y -> x"
       e `shouldBe` "x" @-> "y" @-> "x"
    case E.unann <$> parse P.expr "" "\\(x:Bool) -> \\(y:Int) -> x" of
      Left e -> fail $ show e 
      Right e -> e `shouldBe` ("x", "Bool") @:-> ("y", "Int") @:-> "x"
  
  it "parses application" $ do
    do let Right e = E.unann <$> parse P.expr "" "e1 e2"
       e `shouldBe` "e1" @@ "e2"
    do let Right e = E.unann <$> parse P.expr "" "e1 e2 e3"
       e `shouldBe` ("e1" @@ "e2" @@ "e3")
  
  it "parses annotations" $ do
    case E.unann <$> parse P.expr "" "the (Bool -> Int) (\\x -> 10)" of
      Left e -> fail $ show e
      Right e -> e `shouldBe` ("x" @-> E.nat 10) @:: ("Bool" E.@->: "Int")
    case E.unann <$> parse P.expr "" "the (Bool -> Int -> Int) (\\x -> \\y -> 10)" of
      Left e -> fail $ show e
      Right e -> e `shouldBe` ("x" @-> "y" @-> E.nat 10) @:: ("Bool" E.@->: "Int" E.@->: "Int")
  
  it "parses compound expressions" $ 
    do let Right e = E.unann <$> parse P.expr "" "\\x -> (\\y -> x y, y (True,x))"
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


quasiSpec :: Spec
quasiSpec = do
  it "expression quoter works" $ do
    E.unann expr01 `shouldBe` "x" @-> "y" @-> E.the "Nat" ("x" @@ "y" @@ E.true)
  it "decl quoter works" $ do
    E.unannD decl01 `shouldBe`
      E.datad "Tree" (E.Star E.:->*: E.Star)
                      [ E.constr "Leaf" []
                      , E.constr "Branch" ["a", "Tree" @@: "a", "Tree" @@: "a"]
                      ]
    

expr01 :: P.Expr
expr01 = [unsafeExpr|\x -> \y -> the (Nat) (x y True)|]

decl01, decl02, decl03 :: P.Decl
decl01 = [unsafeDecl|data Tree a = Leaf | Branch a (Tree a) (Tree a).|]
decl02 = undefined
decl03 = undefined

declSpec :: Spec
declSpec = do
  it "parses data type decls" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "data Foo = ."
       decl `shouldBe` E.datad "Foo" E.Star []
    do let Right decl = E.unannD <$> parse P.decl "" "data Foo a = ."
       decl `shouldBe` E.datad "Foo" (E.Star E.:->*: E.Star) []
    do let Right decl = E.unannD <$> parse P.decl "" "data Foo a b = ."
       decl `shouldBe` E.datad "Foo" (E.Star E.:->*: E.Star E.:->*: E.Star) []
    do let Right decl = E.unannD <$> parse P.decl "" "data Unit = MkUnit."
       decl `shouldBe` E.datad "Unit" E.Star [E.constr "MkUnit" []]
    do let Right decl = E.unannD <$> parse P.decl "" "data Bool = True | False."
       decl `shouldBe` E.datad "Bool" E.Star [E.constr "True" [], E.constr "False" []]
    do let Right decl = E.unannD <$> parse P.decl "" "data Maybe a = Nothing | Just a."
       decl `shouldBe` E.datad "Maybe" (E.Star E.:->*: E.Star) [E.constr "Nothing" [], E.constr "Just" ["a"]]
    do let Right decl = E.unannD <$> parse P.decl "" "data List a = Nil | Cons (List a)."
       decl `shouldBe` E.datad "List" (E.Star E.:->*: E.Star) [E.constr "Nil" [], E.constr "Cons" ["List" @@: "a"]]
    do let Right decl = E.unannD <$> parse P.decl "" "data Tree a = Leaf | Branch a (Tree a) (Tree a)."
       E.unannD decl `shouldBe`
          E.datad "Tree" (E.Star E.:->*: E.Star)
                          [ E.constr "Leaf" []
                          , E.constr "Branch" ["a", "Tree" @@: "a", "Tree" @@: "a"]
                          ]

  it "parses function declarations" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "id = \\x -> x."
       decl `shouldBe` E.fund "id" ("x" @-> "x")

  it "parses type signatures" $ do
    do let Right decl = E.unannD <$> parse P.decl "" "id : a -> a."
       decl `shouldBe` E.sigd "id" ("a" @->: "a")

tcSpec :: Spec
tcSpec = do
  it "checks primitives" $ do
    E.checkC0 (E.nat 10) "Nat"  `shouldBe` Right ()
    E.checkC0 E.true     "Bool" `shouldBe` Right ()
    E.checkC0 E.unit     "Unit" `shouldBe` Right ()
    E.checkC0 E.unit     "Bool" `shouldSatisfy` isLeft

  it "checks variables" $ do
    E.checkC (E.ctx [("x", "Nat")]) (E.var "x") "Nat" `shouldBe` Right ()
    E.checkC (E.ctx [("f" ,"Nat" @->: "Nat")]) (E.var "f") ("Nat" @->: "Nat") `shouldBe` Right ()
    E.checkC (E.ctx [("x", "Nat")]) (E.var "x") "Bool" `shouldSatisfy` isLeft
  
  it "checks applications" $ do
    E.checkC (E.ctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.nat 10) "Nat" `shouldBe` Right ()
    E.checkC (E.ctx [("f" , ("Nat" @->: "Bool") @->: "Unit")]) (E.var "f" @@ ("x" @-> E.true)) "Unit" `shouldBe` Right ()
    E.checkC0 (E.the ("Nat" @->: "Nat") ("x" @-> "x") @@ E.nat 10) "Nat" `shouldBe` Right ()
    E.checkC (E.ctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.true)   "Nat" `shouldSatisfy` isLeft
  
  it "checks tuples" $ do
    E.checkC0 [unsafeExpr|(10,20)|] ("Tuple" @@: "Nat" @@: "Nat") `shouldBe` Right ()
    E.checkC (E.ctx [("x", "Nat"), ("f", "Nat" @->: "Bool")]) [unsafeExpr|(x, f x)|] ("Tuple" @@: "Nat" @@: "Bool")
        `shouldBe` Right ()
    E.checkC (E.ctx [("x", "Nat")]) [unsafeExpr|(x, \y -> x)|] ("Tuple" @@: "Nat" @@: ("Bool" @->: "Nat"))
        `shouldBe` Right ()
    E.checkC (E.ctx [("x", "Nat")]) [unsafeExpr|(x, \y -> x)|] ("Tuple" @@: "Nat" @@: ("Bool" @->: "Bool"))
        `shouldSatisfy` isLeft
  
  it "checks lambdas" $ do
    E.checkC0 [unsafeExpr|\x -> x|] ("Nat" @->: "Nat") `shouldBe` Right ()
    E.checkC0 [unsafeExpr|\x -> 10|] ("Nat" @->: "Nat") `shouldBe` Right ()
    E.checkC0 [unsafeExpr|\x -> \y -> x|] ("Bool" @->: "Nat" @->: "Bool") `shouldBe` Right ()
    E.checkC0 [unsafeExpr|\x -> \y -> x|] ("Nat" @->: "Bool" @->: "Nat")  `shouldBe` Right ()
    E.checkC0 [unsafeExpr|\x -> \y -> x|] ("Bool" @->: "Nat" @->: "Nat")  `shouldSatisfy` isLeft
