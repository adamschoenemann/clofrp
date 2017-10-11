{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module CloTT.AST.PrettySpec where

import           Test.Tasty.Hspec

import qualified CloTT.AST.Parsed  as E
import           CloTT.AST.Parsed ((@->:), (@@:))
import           CloTT.AST.Parsed (LamCalc(..))
import           CloTT.QuasiQuoter
import           CloTT.Pretty


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
      pps (E.clocks ["k"] $ E.forAll ["a", "b", "c"] $ ("a" @->: "b") @->: "c") `shouldBe` "∇k. ∀a b c. (a -> b) -> c"

  describe "expressions" $ do
    it "works lol" $ do
      let [a,b,c] = ["a" :: E.Expr(), "b", "c"]
      pps a `shouldBe` "a"
      pps (E.nat 10) `shouldBe` "10"
      pps E.true `shouldBe` "True"
      pps E.unit `shouldBe` "()"
      pps ("a" @-> b)`shouldBe` "\\a -> b"
      pps ("a" @-> "b" @-> c) `shouldBe` "\\a -> \\b -> c"
      pps ("a" @-> "b" @-> a @@ b) `shouldBe` "\\a -> \\b -> a b"
      pps ("Tuple" @@ a @@ b) `shouldBe` "Tuple a b"
      pps ("Tuple" @@ ("Just" @@ a) @@ b) `shouldBe` "Tuple (Just a) b"
      pps ("Tuple" @@ ("a" @-> c) @@ b) `shouldBe` "Tuple (\\a -> c) b"
      pps (E.the "Nat" (E.nat 10)) `shouldBe` "the (Nat) 10"
      pps (E.the ("Nat" @->: "Bool") (E.nat 10)) `shouldBe` "the (Nat -> Bool) 10"
      pps [unsafeExpr|case 10 of | x -> 0|] `shouldBe` "case 10 of | x -> 0"
      ppsw 100 [unsafeExpr|case b of | True -> 0 | False -> 1|] `shouldBe` "case b of | True -> 0 | False -> 1"
  
  describe "type aliases" $ do
    it "works lol" $ do
      pps (E.Alias @() "Seconds" [] "Int") `shouldBe` "type Seconds = Int."
      pps (E.Alias @() "Stream" ["a"] $ "List" @@: "a") `shouldBe` "type Stream a = List a."
      pps (E.Alias @() "Option" ["a"] $ "Maybe" @@: "a") `shouldBe` "type Option a = Maybe a."
      pps (E.Alias @() "Sum" ["a", "b"] $ "Either" @@: "a" @@: "b") `shouldBe` "type Sum a b = Either a b."
      ppsw 80 (E.Alias @() "CList" ["a"] $ E.forAll ["r"] $ ("a" @->: "r" @->: "r") @->: "r" @->: "r")
        `shouldBe` "type CList a = ∀r. (a -> r -> r) -> r -> r."

