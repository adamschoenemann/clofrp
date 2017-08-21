{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}


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
import qualified CloTT.Parser.Prog as P
import qualified CloTT.AST.Parsed  as E
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import qualified Data.Map.Strict   as M

import CloTT.QuasiQuoter

main :: IO ()
main = do
  parser <- testSpec "parsing" parserSpec
  quasi <- testSpec "quasi" quasiSpec
  tc <- testSpec "type checking" tcSpec
  decl <- testSpec "declarations" declSpec
  elab <- testSpec "elaboration" elabSpec
  kindOf <- testSpec "kindOf" kindOfSpec
  let group = Test.Tasty.testGroup "tests" [parser, quasi, tc, decl, elab, kindOf]
  Test.Tasty.defaultMain group

parserSpec :: Spec
parserSpec = do
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
      Right e -> e `shouldBe` ("x" @-> E.nat 10) @:: ("Bool" @->: "Int")
    case E.unann <$> parse P.expr "" "the (Bool -> Int -> Int) (\\x -> \\y -> 10)" of
      Left e -> fail $ show e
      Right e -> e `shouldBe` ("x" @-> "y" @-> E.nat 10) @:: ("Bool" @->: "Int" @->: "Int")
  
  it "parses case statements" $ do
    case E.unann <$> parse P.expr "" "case x of | y -> y" of
      Right e -> e `shouldBe` E.caseof "x" [("y", "y")]
      Left e -> fail $ show e
    case E.unann <$> parse P.expr "" "case x of | Tuple a b -> 10 | y -> y" of
      Right e -> e `shouldBe` E.caseof "x" [(E.match "Tuple" ["a", "b"], E.nat 10), ("y", "y")]
      Left e -> fail $ show e
    case E.unann <$> parse P.expr "" "case x of | Tuple (Cons x y) b -> 10 | y -> y" of
      Right e -> e `shouldBe` E.caseof "x" [(E.match "Tuple" [E.match "Cons" ["x", "y"], "b"], E.nat 10), ("y", "y")]
      Left e -> fail $ show e
    case E.unann <$> parse P.expr "" "case n of | Z -> n | S n' -> n'" of
      Right e -> e `shouldBe` E.caseof "n" [(E.match "Z" [], "n"), (E.match "S" ["n'"], "n'")]
      Left e -> fail $ show e
  
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


quasiSpec :: Spec
quasiSpec = do
  it "expression quoter works" $ do
    E.unann expr01 `shouldBe` "x" @-> "y" @-> E.the "Nat" ("x" @@ "y" @@ E.true)
  it "decl quoter works" $ do
    E.unannD decl01 `shouldBe`
      E.datad "Tree" (Star :->*: Star) ["a"]
                      [ E.constr "Leaf" []
                      , E.constr "Branch" ["a", "Tree" @@: "a", "Tree" @@: "a"]
                      ]
  it "program quoter works (01)" $ do
    E.unannP prog01 `shouldBe`
      E.prog [
        E.sigd "id" ("a" @->: "a")
      , E.fund "id" ("x" @-> "x")
      , E.sigd "twice" ("Nat" @->: "Tuple" @@: "Nat" @@: "Nat")
      , E.fund "twice" ("x" @-> ("x" @* "x"))
      , E.datad "Maybe" 
          (Star :->*: Star)
          ["a"]
          [ E.constr "Nothing" []
          , E.constr "Just" ["a"]
          ]
      , E.datad "List" 
          (Star :->*: Star)
          ["a"]
          [ E.constr "Nil" []
          , E.constr "Cons" ["a", "List" @@: "a"]
          ]
      , E.sigd "head" ("List" @@: "a" @->: "Maybe" @@: "a")
      , E.fund "head" ("xs" @-> "xs")
      ]
  it "program quoter works (02)" $ do
    E.unannP prog02 `shouldBe`
      E.prog [
        E.datad "N" 
          Star
          []
          [ E.constr "Z" []
          , E.constr "S" ["N"]
          ]
      , E.sigd "plus" ("N" @->: "N" @->: "N")
      , E.fund "plus" ("m" @-> "n" @-> E.caseof "m"
          [ (E.match "Z" [], "n")
          , (E.match "S" ["m'"], "S" @@ ("plus" @@ "m'" @@ "n"))
          ]
        )
      ]
    

expr01 :: P.Expr
expr01 = [unsafeExpr|\x -> \y -> the (Nat) (x y True)|]

decl01 :: P.Decl
decl01 = [unsafeDecl|data Tree a = Leaf | Branch a (Tree a) (Tree a).|]

prog01, prog02 :: P.Prog
prog01 = [unsafeProg|
  id : a -> a.
  id = \x -> x.

  twice : Nat -> Tuple Nat Nat.
  twice = \x -> (x, x).

  data Maybe a = Nothing | Just a.
  data List a = Nil | Cons a (List a).

  head : List a -> Maybe a.
  head = \xs -> xs.
|]

prog02 = [unsafeProg|
  data N = Z | S N.
  plus : N -> N -> N.
  plus = \m -> \n -> 
    case m of
      | Z    -> n
      | S m' -> S (plus m' n).
|]

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

tcSpec :: Spec
tcSpec = do
  it "checks primitives" $ do
    E.check0 (E.nat 10) "Nat"  `shouldBe` Right ()
    E.check0 E.true     "Bool" `shouldBe` Right ()
    E.check0 E.unit     "Unit" `shouldBe` Right ()
    E.check0 E.unit     "Bool" `shouldSatisfy` isLeft

  it "checks variables" $ do
    E.check (E.ctx [("x", "Nat")]) (E.var "x") "Nat" `shouldBe` Right ()
    E.check (E.ctx [("f" ,"Nat" @->: "Nat")]) (E.var "f") ("Nat" @->: "Nat") `shouldBe` Right ()
    E.check (E.ctx [("x", "Nat")]) (E.var "x") "Bool" `shouldSatisfy` isLeft
  
  it "checks applications" $ do
    E.check (E.ctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.nat 10) "Nat" `shouldBe` Right ()
    E.check (E.ctx [("f" , ("Nat" @->: "Bool") @->: "Unit")]) (E.var "f" @@ ("x" @-> E.true)) "Unit" `shouldBe` Right ()
    E.check0 (E.the ("Nat" @->: "Nat") ("x" @-> "x") @@ E.nat 10) "Nat" `shouldBe` Right ()
    E.check (E.ctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.true)   "Nat" `shouldSatisfy` isLeft
  
  it "checks tuples" $ do
    E.check0 [unsafeExpr|(10,20)|] ("Tuple" @@: "Nat" @@: "Nat") `shouldBe` Right ()
    E.check @() (E.ctx [("x", "Nat"), ("f", "Nat" @->: "Bool")]) ("x" @* "f" @@ "x") ("Tuple" @@: "Nat" @@: "Bool")
        `shouldBe` Right ()
    E.check @() (E.ctx [("x", "Nat")]) ("x" @* ("y" @-> "x")) ("Tuple" @@: "Nat" @@: ("Bool" @->: "Nat"))
        `shouldBe` Right ()
    E.check @() (E.ctx [("x", "Nat")]) ("x" @* ("y" @-> "x")) ("Tuple" @@: "Nat" @@: ("Bool" @->: "Bool"))
        `shouldSatisfy` isLeft
  
  it "checks lambdas" $ do
    E.check0 [unsafeExpr|\x -> x|]  ("Nat" @->: "Nat") `shouldBe` Right ()
    E.check0 [unsafeExpr|\x -> 10|] ("Nat" @->: "Nat") `shouldBe` Right ()
    E.check0 [unsafeExpr|\x -> \y -> x|] ("Bool" @->: "Nat"  @->: "Bool") `shouldBe` Right ()
    E.check0 [unsafeExpr|\x -> \y -> x|] ("Nat"  @->: "Bool" @->: "Nat")  `shouldBe` Right ()
    E.check0 [unsafeExpr|\x -> \y -> x|] ("Bool" @->: "Nat"  @->: "Nat")  `shouldSatisfy` isLeft
  
  it "fails programs with invalid types (1)" $ do
    let prog = [unsafeProg|
      data Foo a = MkFoo a.
      foo : Foo -> Nat.
      foo = \x -> x.
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "fails programs with invalid types (2)" $ do
    let prog = [unsafeProg|
      data List a = Nil | Cons a (List a a).
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "fails programs with invalid types (3)" $ do
    let prog = [unsafeProg|
      data List = Nil | Cons a (List a).
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "succeeds for mono-types" $ do
    let prog = [unsafeProg|
      data Int = .
      data IntList = Nil | Cons Int IntList.
    |]
    E.checkProg prog `shouldBe` Right ()

  it "succeeds for poly-types" $ do
    let prog = [unsafeProg|
      data List a = Nil | Cons a (List a).
    |]
    E.checkProg prog `shouldBe` Right ()

  it "fails wrong signatures (wrong kind)" $ do
    let prog = [unsafeProg|
      data List a = Nil | Cons a (List a).
      data Int = .
      head : List -> List Int.
      head = \x -> x.
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "fails signatures without explicit foralls" $ do
    let prog = [unsafeProg|
      data List a = Nil | Cons a (List a).
      listId : List a -> List a.
      listId = \x -> x.
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "succeeds with explicit foralls" $ do
    let prog = [unsafeProg|
      data List a = Nil | Cons a (List a).
      listId : forall a. List a -> List a.
      listId = \x -> x.
    |]
    E.checkProg prog `shouldBe` Right ()
  
  it "succeeds with simple id function" $ do
    let prog = [unsafeProg|
      id : forall a. a -> a.
      id = \x -> x.
    |]
    E.checkProg prog `shouldBe` Right ()
  
  it "succeeds with mono-types (1)" $ do
    let prog = [unsafeProg|
      data N = Z | S N.

      zero : N.
      zero = Z.

      one : N.
      one = S Z.

      succ : N -> N.
      succ = \n -> S n.

      plus2 : N -> N.
      plus2 = \n -> succ (succ n).

      -- should fail when we stop having implicit general recursion
      bottom : N -> N.
      bottom = \n -> bottom n.
    |]
    E.checkProg prog `shouldBe` Right ()



elabSpec :: Spec
elabSpec = do
  let two (x,y,z) = (x,y)
  let elabProg prog = two <$> E.elabProg prog

  it "elabs the empty program" $ do
    let prog = [unsafeProg| |]
    elabProg prog `shouldBe` Right (E.emptyk, E.empty)
  
  it "elabs a program with one annotated definition" $ do
    let prog = [unsafeProg|id : Nat -> Nat. id = \x -> x.|]
    elabProg prog `shouldBe` Right (E.emptyk, E.ctx [("id", "Nat" @->: "Nat")])

  it "elabs a program with one data declaration" $ do
    let prog = [unsafeProg|data Maybe a = Nothing | Just a.|]
    elabProg prog `shouldBe`
      Right ( E.ctxk [("Maybe", Star :->*: Star)]
            , E.ctx  [ ("Just", E.forAll ["a"] $ "a" @->: "Maybe" @@: "a")
                     , ("Nothing", E.forAll ["a"] $ "Maybe" @@: "a")
                     ]
            )
  
  it "elabs prog01" $ do
    let Right (ctxk, ctx) = elabProg prog01
    ctxk `shouldBe` E.ctxk [ ("List", Star :->*: Star)
                           , ("Maybe", Star :->*: Star)
                           ]

    M.lookup "Cons"    ctx `shouldBe` Just (E.forAll ["a"] $ "a"     @->: "List"  @@: "a" @->: "List" @@: "a")
    M.lookup "Just"    ctx `shouldBe` Just (E.forAll ["a"] $ "a"     @->: "Maybe" @@: "a")
    M.lookup "Nil"     ctx `shouldBe` Just (E.forAll ["a"] $ "List"  @@: "a")
    M.lookup "Nothing" ctx `shouldBe` Just (E.forAll ["a"] $ "Maybe" @@: "a")
    M.lookup "head"    ctx `shouldBe` Just ("List"  @@: "a" @->: "Maybe" @@: "a")
    M.lookup "twice"   ctx `shouldBe` Just ("Nat"   @->: "Tuple" @@: "Nat" @@: "Nat")
    M.lookup "id"      ctx `shouldBe` Just ("a"     @->: "a")

  it "fails when a definition is missing" $ do
    let prog = [unsafeProg|id : Nat -> Nat.|]
    elabProg prog `shouldSatisfy` isLeft

  it "fails when a signature is missing" $ do
    let prog = [unsafeProg|id = \x -> x.|]
    elabProg prog `shouldSatisfy` isLeft
  
  it "succeeds even when types are not well-formed" $ do
    let prog = [unsafeProg|
      data Foo a = MkFoo a.
      foo : Foo -> Nat.
      foo = \x -> x.
    |]
    let Right (ctxk, ctx) = elabProg prog
    M.lookup "Foo"      ctxk `shouldBe` Just (Star :->*: Star)
    M.lookup "MkFoo"    ctx  `shouldBe` Just (E.forAll ["a"] $ "a"     @->: "Foo" @@: "a")
    M.lookup "foo"      ctx  `shouldBe` Just ("Foo"   @->: "Nat")


kindOfSpec :: Spec
kindOfSpec = do
  let kinds = [ ("List", Star :->*: Star)
              , ("Tuple", Star :->*: Star :->*: Star)
              , ("Nat", Star)
              , ("a", Star)
              , ("b", Star)
              ]
  let [listK, tupK, natK, aK, bK] = kinds

  it "looks up kinds" $ do
    E.kindOf (E.ctxk [natK]) "Nat" `shouldBe` Right Star

  it "infers arrow types to be kind *" $ do
    E.kindOf (E.ctxk [natK]) ("Nat" @->: "Nat") `shouldBe` Right Star
    E.kindOf (E.ctxk [natK, listK]) ("List" @@: "Nat" @->: "List" @@: "Nat") `shouldBe` Right Star

  it "fails when type not found in ctx" $ do
    E.kindOf (E.ctxk []) "Nat" `shouldSatisfy` isLeft
  
  it "fails with partially applied types in arrows" $ do
    E.kindOf (E.ctxk [listK, aK]) ("List" @->: "a") `shouldSatisfy` isLeft

  it "infers lists" $ do
    E.kindOf (E.ctxk [listK, aK]) ("List" @@: "a") `shouldBe` Right Star

  it "infers tuples (curried)" $ do
    E.kindOf (E.ctxk [tupK, aK]) ("Tuple" @@: "a") `shouldBe` Right (Star :->*: Star)

  it "infers tuples" $ do
    E.kindOf (E.ctxk [tupK, aK, bK]) ("Tuple" @@: "a" @@: "b") `shouldBe` Right Star

  it "infers tuples of lists" $ do
    E.kindOf (E.ctxk [tupK, listK, aK, bK]) ("Tuple" @@: ("List" @@: "a") @@: "b") `shouldBe` Right Star

  it "infers foralls" $ do
    E.kindOf (E.ctxk [listK]) (E.forAll ["a"] $ "List" @@: "a") `shouldBe` Right Star
    E.kindOf (E.ctxk [tupK])  (E.forAll ["a", "b"] $ "Tuple" @@: "a" @@: "b") `shouldBe` Right Star
    E.kindOf (E.ctxk [tupK])  (E.forAll ["a"] "a" @->: E.forAll ["a"] "a") `shouldBe` Right Star

