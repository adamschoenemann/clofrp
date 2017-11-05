{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}

module CloTT.EvalSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.String (fromString)

import qualified CloTT.AST.Parsed  as E
import qualified CloTT.AST.Prim    as P
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))

-- import           CloTT.Check
-- import           CloTT.Check.Prog
import qualified Data.Map.Strict as M
-- import           CloTT.QuasiQuoter
-- import           CloTT.Check.TestUtils
import           CloTT.TestUtils
import           CloTT.Pretty
import           CloTT.Eval

evalSpec :: Spec
evalSpec = do
  let eval0 e = runEvalM (evalExpr e) M.empty
  let eval env e = runEvalM (evalExpr e) env
  let nat = Prim . P.Nat
  describe "evalExpr" $ do
    it "evals lambdas" $ do
      eval0 ("x" @-> "x") `shouldBe` Right (Closure M.empty "x" (E.var "x"))
    it "evals applications" $ do
      eval0 (("x" @-> "x") @@ E.nat 10) `shouldBe` Right (nat 10)
      let m = M.fromList [("x", nat 10)]
      eval0 (("x" @-> "y" @-> "x") @@ E.nat 10) `shouldBe` Right (Closure m "y" (E.var "x"))
    

