{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module CloTT.AST.PrettySpec where

import           Test.Tasty.Hspec

import qualified CloTT.AST  as E
import           CloTT.AST ((@->:), (@@:))
import           CloTT.AST (LamCalc(..))
import           CloTT.QuasiQuoter
import           CloTT.Pretty
import           CloTT.TestUtils
import           NeatInterpolation
import           Data.Text (unpack)


prettySpec :: Spec
prettySpec = do
  describe "names" $ do
    it "shows machine-generated names" $ do
      pps (E.free $ E.MName 0) `shouldBe` "`a"
      pps (E.free $ E.MName 1) `shouldBe` "`b"
      pps (E.free $ E.MName 25) `shouldBe` "`z"
      pps (E.free $ E.MName 26) `shouldBe` "`a0"
      pps (E.free $ E.MName 27) `shouldBe` "`b0"
      pps (E.free $ E.MName 52) `shouldBe` "`a1"

  describe "types" $ do
    it "works lol" $ do
      pps ("a" :: E.Type () E.Poly) `shouldBe` "a"
      pps ("a" @->: "b") `shouldBe` "a -> b"
      pps ("a" @->: "b" @->: "c") `shouldBe` "a -> b -> c"
      pps (("a" @->: "b") @->: "c") `shouldBe` "(a -> b) -> c"
      pps ("Tuple" @@: "a" @@: "b") `shouldBe` "Tuple a b"
      pps ("Tuple" @@: ("Maybe" @@: "a") @@: "b") `shouldBe` "Tuple (Maybe a) b"
      pps ("Tuple" @@: ("a" @->: "c") @@: "b") `shouldBe` "Tuple (a -> c) b"
      pps (E.exists "a") `shouldBe` "∃a"
      pps (E.exists "a" @->: "b") `shouldBe` "∃a -> b" 
      pps (E.forAll ["a"] "a") `shouldBe` "∀a. a" 
      pps (E.forAll ["a"] $ "a" @->: "Tuple" @@: "a" @@: "a") `shouldBe` "∀a. a -> Tuple a a" 
      pps (E.forAll ["a"] $ "a" @->: (E.forAll ["b"] $"Tuple" @@: "a" @@: "b")) `shouldBe` "∀a. a -> ∀b. Tuple a b" 
      pps (E.forAll ["a"] $ "a" @->: (E.forAll ["b"] $"Tuple" @@: "a" @@: "b") @->: "a") `shouldBe` "∀a. a -> (∀b. Tuple a b) -> a" 
      pps (E.forAll ["a", "b"] $ "a" @->: "b") `shouldBe` "∀a b. a -> b"
      pps (E.forAll ["a", "b", "c"] $ ("a" @->: "b") @->: "c") `shouldBe` "∀a b c. (a -> b) -> c"
      ppsw 80 (E.clocks ["k"] $ E.forAll ["a", "b", "c"] $ ("a" @->: "b") @->: "c") `shouldBe` "∀(k : Clock) a b c. (a -> b) -> c"
      pps (E.later "k" "a") `shouldBe` "⊳k a"
      pps (E.later "k" ("f" @@: "a")) `shouldBe` "⊳k (f a)"
      pps (E.later "k" (E.later "k0" $ "f" @@: "a")) `shouldBe` "⊳k (⊳k0 (f a))"
      pps (E.later "k" "a" @->: "b") `shouldBe` "(⊳k a) -> b"

  describe "expressions" $ do
    it "works lol" $ do
      let [a,b,c] = ["a" :: E.Expr(), "b", "c"]
      pps a `shouldBe` "a"
      pps (E.int 10) `shouldBe` "10"
      pps E.true `shouldBe` "True"
      pps E.unit `shouldBe` "()"
      pps ("a" @-> b)`shouldBe` "\\a -> b"
      pps ("a" @-> "b" @-> c) `shouldBe` "\\a b -> c"
      pps ("a" @-> "b" @-> a @@ b) `shouldBe` "\\a b -> a b"
      pps (("x", "Unit") @:-> ("y", "Maybe" @@: "a") @:-> E.int 10) `shouldBe` "\\(x : Unit) (y : Maybe a) -> 10"
      pps ("Tuple" @@ a @@ b) `shouldBe` "Tuple a b"
      pps ("Tuple" @@ ("Just" @@ a) @@ b) `shouldBe` "Tuple (Just a) b"
      pps ("Tuple" @@ ("a" @-> c) @@ b) `shouldBe` "Tuple (\\a -> c) b"
      pps (E.the "Nat" (E.int 10)) `shouldBe` "(10 : Nat)"
      pps (E.the ("Nat" @->: "Bool") (E.int 10)) `shouldBe` "(10 : Nat -> Bool)"
      pps [unsafeExpr|case 10 of | x -> 0|] `shouldBe` "case 10 of | x -> 0"
      ppsw 100 [unsafeExpr|case b of | True -> 0 | False -> 1|] `shouldBe` "case b of | True -> 0 | False -> 1"
  
  describe "type aliases" $ do
    it "works lol" $ do
      pps (E.aliasd "Seconds" [] "Int") `shouldBe` "type Seconds = Int."
      pps (E.aliasd "Stream" ["a"] $ "List" @@: "a") `shouldBe` "type Stream a = List a."
      pps (E.aliasd "Option" ["a"] $ "Maybe" @@: "a") `shouldBe` "type Option a = Maybe a."
      pps (E.aliasd "Sum" ["a", "b"] $ "Either" @@: "a" @@: "b") `shouldBe` "type Sum a b = Either a b."
      ppsw 80 (E.aliasd "CList" ["a"] $ E.forAll ["r"] $ ("a" @->: "r" @->: "r") @->: "r" @->: "r")
        `shouldBe` "type CList a = ∀r. (a -> r -> r) -> r -> r."
  
  describe "programs" $ do
    it "works with nonsense program" $ do
      let Right prog = pprog [text|
        main : forall a (k : Clock). |>k (a, F (G Int)).
        main = \x y z ->
          let x' = x : F a
          in x' {a} (foo y) z z.
      |]
      ppsw 1000 prog `shouldBe` (
        "main : ∀a (k : Clock). ⊳k (a, F (G Int)).\n" 
        ++ "main = \\x y z -> let x' = (x : F a) in x' {a} (foo y) z z.")

