{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeApplications #-}


-- Tasty makes it easy to test your code. It is a test framework that can
-- combine many different types of tests into one suite. See its website for
-- help: <http://documentup.com/feuerbach/tasty>.
import qualified Test.Tasty
-- Hspec is one of the providers for Tasty. It provides a nice syntax for
-- writing tests. Its website has more info: <https://hspec.github.io>.
import Test.Tasty.Hspec

import CloTT.Check.MonoSpec
import CloTT.ParserSpec
import CloTT.AST.ElabSpec
import CloTT.QuasiQuoterSpec

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
