{-# LANGUAGE OverloadedStrings #-}

module CloTT.QuasiQuoterSpec where

import           Test.Tasty.Hspec
import qualified CloTT.AST.Parsed  as E
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))

import Fixtures

quasiSpec :: Spec
quasiSpec = do
  it "expression quoter works" $ do
    E.unannE expr01 `shouldBe` "x" @-> "y" @-> E.the "Nat" ("x" @@ "y" @@ E.true)
  it "decl quoter works" $ do
    E.unannD decl01 `shouldBe`
      E.datad "Tree" (Star :->*: Star) ["a"]
                      [ E.constr "Leaf" []
                      , E.constr "Branch" ["a", "Tree" @@: "a", "Tree" @@: "a"]
                      ]
  it "program quoter works (01)" $ do
    E.unannP prog01 `shouldBe`
      E.prog [
        E.sigd "id" ("a" @->: "a")
      , E.fund "id" ("x" @-> "x")
      , E.sigd "twice" ("Nat" @->: "Tuple" @@: "Nat" @@: "Nat")
      , E.fund "twice" ("x" @-> ("x" @* "x"))
      , E.datad "Maybe" 
          (Star :->*: Star)
          ["a"]
          [ E.constr "Nothing" []
          , E.constr "Just" ["a"]
          ]
      , E.datad "List" 
          (Star :->*: Star)
          ["a"]
          [ E.constr "Nil" []
          , E.constr "Cons" ["a", "List" @@: "a"]
          ]
      , E.sigd "head" ("List" @@: "a" @->: "Maybe" @@: "a")
      , E.fund "head" ("xs" @-> "xs")
      ]
  it "program quoter works (02)" $ do
    E.unannP prog02 `shouldBe`
      E.prog [
        E.datad "N" 
          Star
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
    