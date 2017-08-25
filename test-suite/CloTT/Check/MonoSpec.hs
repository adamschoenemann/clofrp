{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module CloTT.Check.MonoSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)

import qualified CloTT.AST.Parsed  as E
import qualified CloTT.Check.Mono  as E
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import           CloTT.QuasiQuoter

import Fixtures

tcSpec :: Spec
tcSpec = do
  it "checks primitives" $ do
    E.check0 (E.nat 10) "Nat"  `shouldBe` Right ()
    E.check0 E.true     "Bool" `shouldBe` Right ()
    E.check0 E.unit     "Unit" `shouldBe` Right ()
    E.check0 E.unit     "Bool" `shouldSatisfy` isLeft

  it "checks variables" $ do
    E.check (E.tyctx [("x", "Nat")]) (E.var "x") "Nat" `shouldBe` Right ()
    E.check (E.tyctx [("f" ,"Nat" @->: "Nat")]) (E.var "f") ("Nat" @->: "Nat") `shouldBe` Right ()
    E.check (E.tyctx [("x", "Nat")]) (E.var "x") "Bool" `shouldSatisfy` isLeft
  
  it "checks applications" $ do
    E.check (E.tyctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.nat 10) "Nat" `shouldBe` Right ()
    E.check (E.tyctx [("f" , ("Nat" @->: "Bool") @->: "Unit")]) (E.var "f" @@ ("x" @-> E.true)) "Unit" `shouldBe` Right ()
    E.check0 (E.the ("Nat" @->: "Nat") ("x" @-> "x") @@ E.nat 10) "Nat" `shouldBe` Right ()
    E.check (E.tyctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.true)   "Nat" `shouldSatisfy` isLeft
  
  it "checks tuples" $ do
    E.check0 [unsafeExpr|(10,20)|] ("Tuple" @@: "Nat" @@: "Nat") `shouldBe` Right ()
    E.check @() (E.tyctx [("x", "Nat"), ("f", "Nat" @->: "Bool")]) ("x" @* "f" @@ "x") ("Tuple" @@: "Nat" @@: "Bool")
        `shouldBe` Right ()
    E.check @() (E.tyctx [("x", "Nat")]) ("x" @* ("y" @-> "x")) ("Tuple" @@: "Nat" @@: ("Bool" @->: "Nat"))
        `shouldBe` Right ()
    E.check @() (E.tyctx [("x", "Nat")]) ("x" @* ("y" @-> "x")) ("Tuple" @@: "Nat" @@: ("Bool" @->: "Bool"))
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
  
  it "succeeds with mutual recursive data" $ do
    let prog = [unsafeProg|
      data Foo = Bar | Baz Baz.
      data Baz = MkBaz Foo.
    |]
    E.checkProg prog `shouldBe` Right ()

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
  
  it "checks pattern matches successfully (prog02)" $ do
    E.checkProg prog02 `shouldBe` Right ()
  
  it "errors when patterns are missing bindings" $ do
    let prog = [unsafeProg|
      data N = Z | S N.
      plus : N -> N -> N.
      plus = \m -> \n -> 
        case m of
          | Z -> n
          | S -> m.
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "errors when patterns have too many bindings" $ do
    let prog = [unsafeProg|
      data N = Z | S N.
      plus : N -> N -> N.
      plus = \m -> \n -> 
        case m of
          | Z    -> n
          | S m' n' -> m'.
    |]
    E.checkProg prog `shouldSatisfy` isLeft

  it "errors when patterns have different types" $ do
    let prog = [unsafeProg|
      data N = Z | S N.
      data Foo = MkFoo.
      plus : N -> N -> N.
      plus = \m -> \n -> 
        case m of
          | Z     -> n
          | MkFoo -> m.
    |]
    -- let Left err = E.checkProg prog in print err
    E.checkProg prog `shouldSatisfy` isLeft

  it "errors when cases have different types" $ do
    let prog = [unsafeProg|
      data N = Z | S N.
      data Foo = MkFoo.
      plus : N -> N -> N.
      plus = \m -> \n -> 
        case m of
          | Z     -> n
          | S m'  -> MkFoo.
    |]
    -- let Left err = E.checkProg prog in print err
    E.checkProg prog `shouldSatisfy` isLeft

  it "errors when matching with wrong constructor" $ do
    let prog = [unsafeProg|
      data N = Z | S N.
      data Foo = MkFoo N.
      plus : N -> N -> N.
      plus = \m -> \n -> 
        case m of
          | MkFoo m' -> m.
    |]
    -- let Left err = E.checkProg prog in print err
    E.checkProg prog `shouldSatisfy` isLeft

  it "works with nested pattern matches" $ do
    let prog = [unsafeProg|
      data N       = Z | S N.
      data NList   = Nil | Cons N NList.
      data Bool    = True | False.

      isZeroes : NList -> Bool.
      isZeroes = \xs -> 
        case xs of
          | Nil -> True
          | Cons Z xs' -> isZeroes xs'
          | Cons (S n) xs' -> False.
    |]
    E.checkProg prog `shouldBe` Right ()
  
  it "works with some mono-morphic examples" $ do
    let prog = [unsafeProg|
      data N       = Z | S N.
      data NList   = Nil | Cons N NList.
      data NMaybe  = NNothing | NJust N.
      data NLMaybe = NLNothing | NLJust NList.
      data Bool    = True | False.

      leq : N -> N -> Bool.
      leq = \m -> \n -> 
        case m of
          | Z -> True
          | S m' -> case n of
            | Z -> False
            | S n' -> leq m' n'.

      head : NList -> NMaybe.
      head = \xs -> 
        case xs of
          | Nil -> NNothing
          | Cons n xs' -> NJust n.
      
      tail : NList -> NLMaybe.
      tail = \xs -> 
        case xs of
          | Nil -> NLNothing
          | Cons n xs' -> NLJust xs'.
      
      append : NList -> NList -> NList.
      append = \xs -> \ys -> 
        case xs of
          | Nil -> ys
          | Cons n xs' -> Cons n (append xs' ys).
      
    |]
    -- let Left err = E.checkProg prog in print err
    E.checkProg prog `shouldBe` Right ()

  -- FIXME: We still don't support polymorphism, so this will fail.
  it "works with some polymorphic examples" $ do
    pending
    -- let prog = [unsafeProg|
    --   data N      = Z | S N.
    --   data List a = Nil | Cons a (List a).

    --   append : List N -> List N -> List N.
    --   append = \xs -> \ys -> 
    --     case xs of
    --       | Nil -> ys
    --       | Cons n xs' -> Cons n (append xs' ys).
    -- |]
    -- -- let Left err = E.checkProg prog in print err
    -- E.checkProg prog `shouldBe` Right ()

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