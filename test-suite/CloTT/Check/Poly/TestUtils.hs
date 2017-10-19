{-# LANGUAGE OverloadedStrings #-}

module CloTT.Check.Poly.TestUtils
  ( module CloTT.Check.Poly.TestUtils
  , module NeatInterpolation
  ) where

import Data.Text.Prettyprint.Doc
import Data.Text (Text, unpack)
import Text.Parsec (ParseError)
import Text.Parsec.Pos (SourcePos)
import Test.Tasty.Hspec
import NeatInterpolation

import CloTT.Check.Poly
import CloTT.AST.Parsed
import CloTT.Parser.Prog (parseProg)
import CloTT.TestUtils
import CloTT.Pretty


swidth :: Num a => a
swidth = 2000

shouldYield :: (Show a1, Pretty a1, Show a2, Eq a2) 
            => (Either a1 a2, t, TypingWrite a) -> a2 -> Expectation
shouldYield (res, st, tree) ctx = 
  case res of
    Right ctx' -> do 
      -- failure (showTree tree)
      ctx' `shouldBe` ctx
    Left err   -> do 
      failure $ showW swidth $ pretty err <> "\nProgress:\n" <> prettyTree tree

shouldFail :: (Show a, Show b) => (Either a b, t1, TypingWrite ann) -> Expectation
shouldFail (res, st, tree) = 
  case res of
    Left err -> True `shouldBe` True
    Right x  -> failure (show x ++ "\n" ++ (showW swidth . prettyTree $ tree))

shouldFailWith :: (Show a, Show b) => (Either a b, t1, TypingWrite ann) -> (a -> Expectation) -> Expectation
shouldFailWith (res, st, tree) fn = 
  case res of
    Left err -> fn err
    Right x  -> failure (show x ++ "\n" ++ (showW swidth . prettyTree $ tree))

pprog :: Text -> Either ParseError (Prog SourcePos)
pprog = parseProg . unpack