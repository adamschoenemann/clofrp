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
  let eval environ e = runEvalM (evalExpr e) environ
  let int = Prim . IntVal
  let constr nm vs = Constr nm vs
  let env :: [(E.Name, Value ())]  -> M.Map E.Name (Value ())
      env xs = M.fromList xs
  let (|->) = \x y -> (x,y)
  describe "evalExpr" $ do
    it "evals lambdas" $ do
      eval0 ("x" @-> "x") `shouldBe` Right (Closure M.empty "x" (E.var "x"))
    it "evals applications" $ do
      eval0 (("x" @-> "x") @@ E.nat 10) `shouldBe` Right (int 10)
      let m = env ["x" |-> int 10]
      eval0 (("x" @-> "y" @-> "x") @@ E.nat 10) `shouldBe` Right (Closure m "y" (E.var "x"))
    it "evals contructors (1)" $ do
      let m = env ["S" |-> constr "S" [], "Z" |-> constr "Z" []]
      eval m ("S" @@ "Z") `shouldBe` Right (constr "S" [constr "Z" []])
    it "evals contructors (2)" $ do
      let m = env ["S" |-> constr "S" [], "Z" |-> constr "Z" [], "Cons" |-> constr "Cons" [], "Nil" |-> constr "Nil" []]
      let explist = foldr (\x acc -> "Cons" @@ x @@ acc) "Nil"
      let vallist = foldr (\x acc -> constr "Cons" [x, acc]) (constr "Nil" [])
      eval m (explist $ map E.nat [1..5]) `shouldBe` Right (vallist $ map int [1..5])

    

