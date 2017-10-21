{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.Poly.ClockSpec where

import Test.Tasty.Hspec

import CloTT.Check.Poly.TestUtils
import CloTT.QuasiQuoter
import CloTT.Check.Poly.Prog
import CloTT.Check.Poly.TypingM
import CloTT.AST.Kind
import CloTT.Context
import CloTT.TestUtils
import CloTT.Pretty

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

    it "accepts veeery simple programs with clock application (1)" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        idk : clocks k. forall a. a -> a.
        idk = /\k -> \x -> x. 

        bar : clocks k. Unit.
        bar = /\k -> idk [k] MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "accepts veeery simple programs with clock application (2)" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        idk : clocks k k'. forall a. a -> a.
        idk = /\k k' -> \x -> x. 

        bar : clocks k. Unit.
        bar = /\k -> idk [k] [k] MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "rejects veeery simple programs with clock application (1)" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        idk : clocks k. forall a. a -> a.
        idk = /\k -> \x -> x. 

        bar : clocks k. Unit.
        bar = /\k -> idk MkUnit.
      |]
      runCheckProg mempty prog `shouldFailWith` (errs $ Other "Expected MkUnit to be a clock")
    
    it "checks program with data-decl and clocks" $ do
      let Right prog = pprog [text|
        data NowOrNext (k : Clock) a = Now a | Next (|>k a).
        data Bool = True | False.

        isNow : forall (k : Clock) a. NowOrNext k a -> Bool.
        isNow = \x -> case x of
          | Now y -> True
          | Next y -> False.

        not : Bool -> Bool.
        not = \b -> case b of 
          | True -> False
          | False -> True.

        isNext : forall (k : Clock) a. NowOrNext k a -> Bool.
        isNext = \x -> not (isNow x).
        
        nextOrElse : forall (k : Clock) a. |>k a -> NowOrNext k a -> |>k a.
        nextOrElse = \d non ->
          case non of
            | Now y -> d
            | Next y -> y.

      |]
      let (Right ep, st, wrt) = runTypingM0 (elabProg prog) mempty 
      case query "NowOrNext" (kinds ep ) of
        Just k -> k `shouldBe` ClockK :->*: Star :->*: Star
        Nothing -> failure "NowOrNext"
      runCheckProg mempty prog `shouldYield` ()
    
    it "accepts simple prog with tick abstraction" $ do
      let Right prog = pprog [text|
        tid : forall (k : Clock) a. |>k a -> |>k a.
        tid = \d -> \\(af : k) -> d {af}.
      |]
      runCheckProg mempty prog `shouldYield` ()
      
      