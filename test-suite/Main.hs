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

import CloTT.ParserSpec
import CloTT.QuasiQuoterSpec
import CloTT.Check.PolySpec
import CloTT.Check.Poly.ProgSpec
import CloTT.Check.Poly.ClockSpec
import CloTT.AST.PrettySpec


main :: IO ()
main = do
  parser <- testSpec "parsing" parserSpec
  quasi <- testSpec "quasi" quasiSpec
  poly <- testSpec "poly-type checking" polySpec
  decl <- testSpec "declarations" declSpec
  pretty <- testSpec "pretty" prettySpec
  checkProg <- testSpec "checkProg" progSpec
  clocks <- testSpec "clockSpec" clockSpec
  let group = Test.Tasty.testGroup "tests" [parser, quasi, poly, decl, pretty, checkProg, clocks]
  Test.Tasty.defaultMain group
