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
  let eval e = runEvalM (evalExpr e) M.empty
  describe "evalExpr" $ do
    it "evals lambdas" $ do
      eval ("x" @-> "x") `shouldBe` Right (Closure M.empty "x" (E.var "x"))
    

