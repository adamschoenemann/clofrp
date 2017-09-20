{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}

module CloTT.AST.ElabSpec where

import           Test.Tasty.Hspec
import qualified Data.Map.Strict   as M

import qualified CloTT.AST.Parsed  as E
import qualified CloTT.AST.Elab    as E
import qualified CloTT.Check.Mono  as E
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.QuasiQuoter

import CloTT.TestUtils
import Fixtures

elabSpec :: Spec
elabSpec = do
  let shouldFailElab prog = 
        case E.elabProg prog of
          Left err -> success
          Right ep -> failure $ "Expected elaboration failure but succeeded with " ++ show ep
  let shouldElabTo prog (ks, ts) = 
        case E.elabProg prog of
          Left err -> fail . show $ err
          Right (E.ElabProg {E.kinds, E.types, E.defs, E.destrs}) -> 
            (kinds `shouldBe` ks) >> (types `shouldBe` ts)

  it "elabs the empty program" $ do
    let prog = [unsafeProg| |]
    prog `shouldElabTo` (E.emptyk, E.emptyt)
  
  it "elabs a program with one annotated definition" $ do
    let prog = [unsafeProg|id : Nat -> Nat. id = \x -> x.|]
    prog `shouldElabTo` (E.emptyk, E.tymap [("id", "Nat" @->: "Nat")])

  it "elabs a program with one data declaration" $ do
    let prog = [unsafeProg|data Maybe a = Nothing | Just a.|]
    prog `shouldElabTo`
            ( E.ctxk [("Maybe", Star :->*: Star)]
            , E.tymap  [ ("Just", E.forAll ["a"] $ "a" @->: "Maybe" @@: "a")
                       , ("Nothing", E.forAll ["a"] $ "Maybe" @@: "a")
                     ]
            )
  
  it "elabs prog01" $ do
    let Right (E.ElabProg {E.kinds = ctxk, E.types = ctx}) = E.elabProg prog01
    ctxk `shouldBe` E.ctxk [ ("List", Star :->*: Star)
                           , ("Maybe", Star :->*: Star)
                           ]

    M.lookup "Cons"    ctx `shouldBe` Just (E.forAll ["a"] $ "a"     @->: "List"  @@: "a" @->: "List" @@: "a")
    M.lookup "Just"    ctx `shouldBe` Just (E.forAll ["a"] $ "a"     @->: "Maybe" @@: "a")
    M.lookup "Nil"     ctx `shouldBe` Just (E.forAll ["a"] $ "List"  @@: "a")
    M.lookup "Nothing" ctx `shouldBe` Just (E.forAll ["a"] $ "Maybe" @@: "a")
    M.lookup "head"    ctx `shouldBe` Just ("List"  @@: "a" @->: "Maybe" @@: "a")
    M.lookup "twice"   ctx `shouldBe` Just ("Nat"   @->: "Tuple" @@: "Nat" @@: "Nat")
    M.lookup "id"      ctx `shouldBe` Just ("a"     @->: "a")

  it "fails when a definition is missing" $ do
    let prog = [unsafeProg|id : Nat -> Nat.|]
    shouldFailElab prog

  it "fails when a signature is missing" $ do
    let prog = [unsafeProg|id = \x -> x.|]
    shouldFailElab prog
  
  it "succeeds even when types are not well-formed" $ do
    let prog = [unsafeProg|
      data Foo a = MkFoo a.
      foo : Foo -> Nat.
      foo = \x -> x.
    |]
    let Right (E.ElabProg {E.kinds = ctxk, E.types = ctx}) = E.elabProg prog
    M.lookup "Foo"      ctxk `shouldBe` Just (Star :->*: Star)
    M.lookup "MkFoo"    ctx  `shouldBe` Just (E.forAll ["a"] $ "a"     @->: "Foo" @@: "a")
    M.lookup "foo"      ctx  `shouldBe` Just ("Foo"   @->: "Nat")