{-# LANGUAGE OverloadedStrings #-}

module CloTT.Check.Poly.TestUtils where

import Data.Text.Prettyprint.Doc
import Test.Tasty.Hspec

import CloTT.Check.Poly
import CloTT.TestUtils
import CloTT.Pretty

shouldYield :: (Show a1, Pretty a1, Show a2, Eq a2) 
            => (Either a1 a2, t, TypingWrite a) -> a2 -> Expectation
shouldYield (res, st, tree) ctx = 
  case res of
    Right ctx' -> do 
      -- failure (showTree tree)
      ctx' `shouldBe` ctx
    Left err   -> do 
      failure $ showW 200 $ pretty err <> "\nProgress:\n" <> prettyTree tree

shouldFail :: (Show a, Show b) => (Either a b, t1, TypingWrite ann) -> Expectation
shouldFail (res, st, tree) = 
  case res of
    Left err -> True `shouldBe` True
    Right x  -> failure (show x ++ "\n" ++ (showW 200 . prettyTree $ tree))

shouldFailWith :: (Show a, Show b) => (Either a b, t1, TypingWrite ann) -> (a -> Expectation) -> Expectation
shouldFailWith (res, st, tree) fn = 
  case res of
    Left err -> fn err
    Right x  -> failure (show x ++ "\n" ++ (showW 200 . prettyTree $ tree))