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
import NeatInterpolation
import Debug.Trace
import Control.DeepSeq

import qualified CloTT.AST.Parsed  as E
import qualified CloTT.AST.Prim    as P
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))

-- import           CloTT.Check
-- import           CloTT.Check.Prog
import qualified Data.Map.Strict as M
import           CloTT.QuasiQuoter
-- import           CloTT.Check.TestUtils
import           CloTT.TestUtils
import           CloTT.Pretty
import           CloTT.Eval
import           CloTT.Annotated (unann)

evalSpec :: Spec
evalSpec = do
  let eval0 e = runEvalM (evalExprStep e) mempty
  let eval environ e = runEvalM (evalExprStep e) environ
  let int = Prim . IntVal
  let constr nm vs = Constr nm vs
  let c nm = (nm, Constr nm [])
  let (|->) = \x y -> (x,y) 
  let [s,z,cons,nil,just,nothing] = [c "S", c "Z", c "Cons", c "Nil", c "Just", c "Nothing"] :: [(E.Name, Value ())]
  describe "evalExprStep" $ do
    it "evals lambdas" $ do
      eval0 ("x" @-> "x") `shouldBe` Right (Closure [] "x" (E.var "x"))
    it "evals applications" $ do
      eval0 (("x" @-> "x") @@ E.int 10) `shouldBe` Right (int 10)
      let m = ["x" |-> int 10]
      eval0 (("x" @-> "y" @-> "x") @@ E.int 10) `shouldBe` Right (Closure m "y" (E.var "x"))
    it "evals tuples" $ do
      eval0 (("x" @-> E.tup ["x", E.int 10]) @@ E.int 9) `shouldBe` Right (Tuple [int 9, int 10])

    it "evals contructors (1)" $ do
      let m = [s, z]
      eval m ("S" @@ "Z") `shouldBe` Right (constr "S" [constr "Z" []])
    it "evals contructors (2)" $ do
      let m = [s,z,nil,cons]
      let explist = foldr (\x acc -> "Cons" @@ x @@ acc) "Nil"
      let vallist = foldr (\x acc -> constr "Cons" [x, acc]) (constr "Nil" [])
      eval m (explist $ map E.int [1..5]) `shouldBe` Right (vallist $ map int [1..5])
    it "evals contructors (3)" $ do
      let m = [s,z,just,nothing]
      let p = unann [unsafeExpr|
        S (S (S Z))
      |]
      let s' arg = Constr "S" [arg]
      eval m p `shouldBe` Right (s' $ s' $ s' (Constr "Z" []))
    it "evals contructors (4)" $ do
      let m = [s,z,just,nothing]
      let p = unann [unsafeExpr|
        let s = S in
        let z = Z in
        s (s (s z))
      |]
      let s' arg = Constr "S" [arg]
      eval m p `shouldBe` Right (s' $ s' $ s' (Constr "Z" []))
    -- it "evals contructors (3)" $ do
    --   let m = env [s,z,just,nothing]
    --   let p = unann [unsafeExpr
    --     let map = \f x -> case x of | Nothing -> Nothing | Just x' -> Just (f x') in
    --   |]
    --   eval m () `shouldBe` Right (vallist $ map int [1..5])

    it "evals let bindings (1)" $ do
      eval0 (unann [unsafeExpr| let x = 10 in let id = \y -> y in id x |]) `shouldBe` Right (int 10)
    it "evals let bindings (2)" $ do
      eval0 (unann [unsafeExpr| let x = 9 in let id = \x -> x in (id x, id id 10, id id id 11) |]) `shouldBe` Right (Tuple [int 9, int 10, int 11])
    it "evals let bindings (3)" $ do
      let m = [c "Wrap"]
      eval m (unann [unsafeExpr| (\x -> let Wrap x' = x in x') (Wrap 10) |]) `shouldBe` Right (int 10)

    describe "case expression evaluation" $ do
      let p1 e = unann [unsafeExpr|
        (\x -> case x of
          | Nothing -> 0
          | Just x -> x
        )
      |] @@ e
      let m = [s,z,just,nothing,cons,nil]
      it "evals case expressions (1)" $ do
        eval m (p1 ("Just" @@ E.int 10)) `shouldBe` Right (int 10)
      it "evals case expressions (2)" $ do
        eval m (p1 "Nothing") `shouldBe` Right (int 0)

      let p2 e = unann [unsafeExpr|
        (\x -> case x of
          | Nothing -> 0
          | Just Nil -> 1
          | Just (Cons x' xs') -> x'
        ) 
      |] @@ e
      it "evals case expressions (3)" $ do
        eval m (p2 ("Just" @@ ("Cons" @@ E.int 10 @@ "Nil"))) `shouldBe` Right (int 10)
      it "evals case expressions (4)" $ do
        eval m (p2 ("Just" @@ "Nil")) `shouldBe` Right (int 1)

      let p3 e = unann [unsafeExpr|
        \x -> case x of
          | z -> 10
          | (x, y) -> x
      |] @@ e

      it "evals case expressions (5)" $ do
        eval m (p3 (E.tup [E.int 1, E.int 2])) `shouldBe` Right (int 10)
    
    describe "fixpoints" $ do
      it "evals first iter of const stream correctly" $ do
        {-
          -- fix body => body (\\af -> fix body)

          fix body => 
          body (\\af -> body) =>
          (\xs -> fold (Cons x xs)) (\\af -> fix body) =>
          fold (Cons x (\\af -> fix body)) =>
          Cons x (\\af -> fix body) =>
          Cons x (body (\\af -> fix body)) =>
          Cons x (Cons x (\\af -> fix body))
        -}
        let p = unann [unsafeExpr|
          (\x -> let body = \xs -> fold (Cons x xs)
                 in  fix body
          ) 1
        |]
        let m = [cons]
        case eval m p of 
          Right (Constr "Cons" [Prim (IntVal 1), TickClosure _ (E.DeBruijn 0) b]) -> 
            b `shouldBe` (E.fixp @@ "body")
          Right e  -> failure ("did not expect " ++ show (pretty e))
          Left err -> failure (show err)

      it "evals first iter of map correctly" $ do
        {-
          map S (const Z) =>
          fix mapfix (const Z) =>
          mapfix (\\af -> fix mapfix) (const Z) =>
          cons (S Z) (\\af -> mapfix [af] (xs' [af])) =>
          fold (Cons (S Z) (\\af -> mapfix [af] (xs' [af]))) =>
          Cons (S Z) (\\af -> mapfix [af] (xs' [af])) =>
        -}
        let p = unann [unsafeExpr|
          let cons = \x xs -> fold (Cons x xs) in 
          let map = \f -> 
            let mapfix = \g xs ->
                case unfold xs of
                | Cons x xs' -> 
                  let ys = \\(af : k) -> g [af] (xs' [af])
                  in  cons (f x) ys 
            in fix mapfix in
          let const = \x ->
             let body = \xs -> Cons x xs
             in  fix body
          in map S (const Z)
        |]
        let m = [s,z,cons]
        case eval m p of 
          Right (Constr "Cons" [Constr "S" [Constr "Z" []], TickClosure _ _ e]) ->
            e `shouldBe` "g" @@ "[af]" @@ ("xs'" @@ "[af]")
          Right e  -> failure ("did not expect " ++ show (pretty e))
          Left err -> failure (show err)
    
  describe "evalExprUntil" $ do
    let evforever environ x = 
          let term i = traceShow i $ if i < 100 then (False, succ i) else (True, i) 
          in  runEvalM (evalExprUntil x (0 :: Int) term) environ

    let evforever0 x = evforever mempty x
    -- it "forever terminates with primitives" $ do
    --   evforever0 (E.int 10) `shouldBe` Right (int 10)
    --   evforever [just] ("Just" @@ E.int 10) `shouldBe` Right (Constr "Just" [int 10])

    -- it "forever terminates with 2-step comp" $ do
    --   let e = "Cons" @@ E.int 1 @@ (("af", "k") `E.tAbs` ("Cons" @@ E.int 2 @@ "Nil"))
    --   evforever [cons, nil] e `shouldBe` Right (Constr "Cons" [int 1, Constr "Cons" [int 2, Constr "Nil" []]])
    
    it "forever evals the constant stream" $ do
      let Right p = pexprua [text|
        let const = \x ->
            let body = \xs -> Cons x xs
            in  fix body
        in const Z
      |]
      let m = [s,z,cons]
      let Right cs = evforever m p
      -- let cs = foldr (\x acc -> Constr "Cons" [acc]) (Constr @() "Nil" []) $ repeat 0
      putStrLn "--------------------------------------"
      putStrLn . show $ takeConstr 10 $ cs
      -- _ <- deepseq cs (pure ())
      putStrLn "--------------------------------------"
      True `shouldBe` True
      

-- takes n levels down in a tree of constructors
takeConstr :: Int -> Value a -> Value a
takeConstr n v 
  | n <= 0    = Constr "__STOPPED__" []
  | otherwise = 
      case v of
        Constr nm [] -> v
        Constr nm vs -> Constr nm (map (takeConstr (n-1)) vs)
        _            -> v