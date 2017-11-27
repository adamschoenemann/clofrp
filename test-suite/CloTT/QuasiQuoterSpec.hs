{-# LANGUAGE OverloadedStrings #-}

module CloTT.QuasiQuoterSpec where

import           Test.Tasty.Hspec
import qualified CloTT.AST  as E
import           CloTT.AST ((@->:), (@@:), Kind(..))
import           CloTT.AST (LamCalc(..))

import qualified Fixtures

quasiSpec :: Spec
quasiSpec = do
  it "expression quoter works" $ do
    E.unannE Fixtures.expr01 `shouldBe` "x" @-> "y" @-> E.the (E.free "Nat") ("x" @@ "y" @@ E.true)
  it "decl quoter works" $ do
    E.unannD Fixtures.decl01 `shouldBe`
      E.datad "Tree"  [("a", Star)]
                      [ E.constr "Leaf" []
                      , E.constr "Branch" ["a", "Tree" @@: "a", "Tree" @@: "a"]
                      ]
  it "program quoter works (01)" $ do
    E.unannP Fixtures.prog01 `shouldBe`
      E.prog [
        E.sigd "id" ("a" @->: "a")
      , E.fund "id" ("x" @-> "x")
      , E.sigd "twice" ("Nat" @->: "Tuple" @@: "Nat" @@: "Nat")
      , E.fund "twice" ("x" @-> (E.tup ["x", "x"]))
      , E.datad "Maybe" 
          [("a", Star)]
          [ E.constr "Nothing" []
          , E.constr "Just" ["a"]
          ]
      , E.datad "List" 
          [("a", Star)]
          [ E.constr "Nil" []
          , E.constr "Cons" ["a", "List" @@: "a"]
          ]
      , E.sigd "head" ("List" @@: "a" @->: "Maybe" @@: "a")
      , E.fund "head" ("xs" @-> "xs")
      ]
  it "program quoter works (02)" $ do
    E.unannP Fixtures.prog02 `shouldBe`
      E.prog [
        E.datad "N" 
          []
          [ E.constr "Z" []
          , E.constr "S" ["N"]
          ]
      , E.sigd "plus" ("N" @->: "N" @->: "N")
      , E.fund "plus" ("m" @-> "n" @-> E.caseof "m"
          [ (E.match "Z" [], "n")
          , (E.match "S" ["m'"], "S" @@ ("plus" @@ "m'" @@ "n"))
          ]
        )
      ]
    