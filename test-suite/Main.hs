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

import CloFRP.ParserSpec
import CloFRP.QuasiQuoterSpec
import CloFRP.CheckSpec
import CloFRP.Check.ProgSpec
import CloFRP.Check.ClockSpec
import CloFRP.Check.RecSpec
import CloFRP.Check.HigherKinded
import CloFRP.AST.PrettySpec
import CloFRP.EvalSpec
import CloFRP.DeriveSpec
import CloFRP.InteropSpec


main :: IO ()
main = do
  parser <- testSpec "parsing" parserSpec
  quasi <- testSpec "quasi" quasiSpec
  typecheck <- testSpec "type checking" typecheckSpec
  decl <- testSpec "declarations" declSpec
  pretty <- testSpec "pretty" prettySpec
  checkProg <- testSpec "checkProg" progSpec
  clocks <- testSpec "clockSpec" clockSpec
  recursive <- testSpec "recursive types" recSpec
  higherKinded <- testSpec "higher kinded types" higherKindedSpec
  eval <- testSpec "evaluation" evalSpec
  derive <- testSpec "derivation" deriveSpec
  interop <- testSpec "interop" interopSpec
  let group = Test.Tasty.testGroup "tests" [parser, quasi, typecheck, decl, pretty, checkProg, clocks, recursive, higherKinded, eval, derive, interop]
  Test.Tasty.defaultMain group
