{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.Poly.ClockSpec where

import Test.Tasty.Hspec

import           CloTT.Check.Poly.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Check.Poly.Prog
import           CloTT.Check.Poly.TypingM
import           CloTT.Pretty
import           CloTT.AST.Name

clockSpec :: Spec 
clockSpec = do
  let errs e x = fst x `shouldBe` e
  describe "clocks" $ do
    it "accepts veeery simple programs with clock quantification" $ do
      let prog = [unsafeProg|
        foo : clocks k. forall a. a -> a.
        foo = /\k -> \x -> x. 
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "rejects veeery simple programs with clock quantification" $ do
      let prog = [unsafeProg|
        foo : clocks k. forall a. a -> a.
        foo = /\k' -> \x -> x. 
      |]
      runCheckProg mempty prog `shouldFailWith` (errs $ Other "Clock k' must be named k")

    it "accepts veeery simple programs with clock application" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        idk : clocks k. forall a. a -> a.
        idk = /\k -> \x -> x. 

        bar : clocks k. Unit.
        bar = /\k -> idk [k] MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()
      