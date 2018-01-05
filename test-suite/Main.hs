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
import CloFRP.EvalSpec (evalSpec)
import CloFRP.DeriveSpec
import CloFRP.InteropSpec
import CloFRP.CompilerSpec


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
  compiler <- testSpec "compiler" compilerSpec
  let group = Test.Tasty.testGroup "tests" [parser, quasi, typecheck, decl, pretty, checkProg, clocks, recursive, higherKinded, eval, derive, interop, compiler]
  Test.Tasty.defaultMain group

data Tree a = Leaf | Branch a (Tree a) (Tree a) deriving (Eq, Show)

getChildren :: [Tree a] -> [Tree a]
getChildren xs = concatMap children xs where
  children Leaf = []
  children (Branch x l r) = [l,r]

rebuild :: [Tree a] -> [Tree a] -> [Tree a]
rebuild [] _ = []
rebuild _ [] = []
rebuild (Leaf : ps) cs = Leaf : rebuild ps cs
rebuild (Branch x l r : ps) (l' : r' : cs) = Branch x l' r' : rebuild ps cs

idTree :: Tree a -> Tree a
idTree t = let cs = getChildren [t]
           in  head $ rebuild [t] cs

mkTree :: Int -> Int -> (Tree Int, Int)
mkTree i n 
  | n <= 0 = (Leaf, i)
  | otherwise = 
    let (l, li) = mkTree (i+1) (n-1) 
        (r, ri) = mkTree li (n-1)
    in  (Branch i l r, ri)