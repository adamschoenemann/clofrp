{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE KindSignatures #-}

module CloFRP.CompilerSpec where

import Prelude hiding (negate)
import Test.Tasty.Hspec
import CloFRP.Compiler
import CloFRP.QuasiQuoter


[hsclofrp|
  extern data Bool = True | False.

  cfp_id : forall a. a -> a.
  cfp_id = \x -> x.

  false : Bool.
  false = False.

  negate : Bool -> Bool.
  negate = \b ->
    case b of
    | True -> False
    | False -> True.
|]
compilerSpec :: Spec
compilerSpec = do
  describe "compiler expressions" $ do
    it "works with id function" $ do
      [hsclofrp| \x -> x |] True `shouldBe` True
    it "works with literals" $ do
      [hsclofrp| 10 |] `shouldBe` (10 :: Integer)
    it "works with tick-abstractions" $ do
      [hsclofrp| \\(af : k) -> 10 |] () `shouldBe` (10 :: Integer)
    it "works with multi-param lambdas" $ do
      [hsclofrp| \x y -> x |] 10 () `shouldBe` (10 :: Integer)
  describe "compiler declarations" $ do
    specify "cfp_id" $ do
      cfp_id True `shouldBe` True
      cfp_id () `shouldBe` ()
      negate True `shouldBe` False
      negate False `shouldBe` True