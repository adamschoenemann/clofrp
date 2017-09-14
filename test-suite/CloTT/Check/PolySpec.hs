{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.PolySpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.Text.Prettyprint.Doc (Pretty)

import qualified CloTT.AST.Parsed  as E
import           CloTT.Check.Poly
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import           CloTT.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Pretty (pps)

-- import Fixtures


-- foo :: forall a. ()
-- foo = ()

shouldYield :: (Show a1, Pretty a1, Show a2, Eq a2) 
            => (Either a1 a2, t, TypingWrite a) -> a2 -> Expectation
shouldYield (res, st, tree) ctx = 
  case res of
    Right ctx' -> ctx' `shouldBe` ctx
    Left err   -> failure $ pps err ++ "\nProgress:\n" ++ showTree tree

shouldFail :: (Show a, Show b) => (Either a b, t1, t) -> Expectation
shouldFail (res, st, tree) = res `shouldSatisfy` isLeft

polySpec :: Spec
polySpec = do
  let nil = emptyCtx @()
  let (.:) = HasType

  describe "splitCtx" $ do
    it "fails for empty context" $ do
      let ctx = nil
      splitCtx' (uni "a") ctx `shouldBe` Nothing
    it "fails for context without el" $ do
      do let ctx = nil <+ uni "b"
         splitCtx' (uni "a") ctx `shouldBe` Nothing
      do let ctx = nil <+ exists "a"
         splitCtx' (uni "a") ctx `shouldBe` Nothing
      do let ctx = nil <+ uni "b" <+ exists "a"
         splitCtx' (uni "a") ctx `shouldBe` Nothing
    it "works for context with el" $ do
      do let ctx = nil <+ uni "b"
         splitCtx' (uni "b") ctx `shouldBe` Just (emptyCtx, uni "b", emptyCtx)
      do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
         let ctx = nil <+ uni "b" <++ xs
         splitCtx' (uni "b") ctx `shouldBe` Just (emptyCtx, uni "b", xs)
      do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
         let ctx = xs <+ uni "b"
         splitCtx' (uni "b") ctx `shouldBe` Just (xs, uni "b", emptyCtx)
      do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
         let ys = nil <+ uni "z" <+ exists "u" <+ marker "v"
         let ctx = xs <+ uni "b" <++ ys
         splitCtx' (uni "b") ctx `shouldBe` Just (xs, uni "b", ys)
      do let id' = "x" .: E.forAll ["a"] ("a" @->: "a")
         let ctx = nil <+ id' <+ exists "a"
         splitCtx' (exists "a") ctx `shouldBe` Just (nil <+ id', exists "a", nil)
    specify "if splitCtx' alpha ctx == (xs, alpha, ys) then ctx == xs <+ alpha <++ ys" $ do
      let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
      let ys = nil <+ uni "z" <+ exists "u" <+ marker "v"
      let ctx = xs <+ uni "b" <++ ys
      let Just (xs', b, ys') = splitCtx' (uni "b") ctx
      ctx `shouldBe` xs' <+ b <++ ys'

  describe "before'" $ do
    it "fails on empty context" $ do
      let ctx = Gamma @() []
      before' (Exists "a") (Exists "b") ctx `shouldBe` False
    it "fails on singleton context" $ do
      let ctx = Gamma @() [exists "a"]
      before' (exists "a") (exists "b") ctx `shouldBe` False
    it "before' a b (.,a,b) == True" $ do
      let ctx = nil <+ exists "a" <+ exists "b"
      before' (exists "a" ) (exists "b") ctx `shouldBe` True
    it "before' a b (T,a,T',b,T'') == True" $ do
      let t  = nil <+ uni "x" <+ exists "z"
      let t' = nil <+ uni "x'" <+ exists "z'" 
      let t'' = nil <+ uni "x''" <+ exists "z''" 
      let ctx = t <+ exists "a" <++ t' <+ exists "b" <++ t''
      putStrLn . show $ ctx
      before' (exists "a") (exists "b") ctx `shouldBe` True
    it "before' a b (.,b,a) == False" $ do
      let ctx = nil <+ exists "b" <+ exists "a"
      before' (exists "a") (exists "b") ctx `shouldBe` False
    it "before' a b (.,b,T,a) == False" $ do
      let t   = nil <+ uni "x" <+ exists "y"
      let ctx = nil <+ exists "b" <++ t <+ exists "a"
      before' (exists "a") (exists "b") ctx `shouldBe` False

  describe "assign'" $ do
    it "fails for empty context" $ do
      let ctx = nil
      assign' "a" "Unit" ctx `shouldBe` Nothing

    it "fails for singleton context without 'a^'" $ do
      let ctx = nil <+ exists "b"
      assign' "a" "Unit" ctx `shouldBe` Nothing

    it "fails for singleton context without 'a^' but with 'a'" $ do
      let ctx = nil <+ uni "a"
      assign' "a" "Unit" ctx `shouldBe` Nothing

    it "fails for context without 'a^' but with 'a'" $ do
      let ctx = nil <+ uni "a" <+ exists "b" <+ marker "c"
      assign' "a" "Unit" ctx `shouldBe` Nothing

    it "works for context with 'a^'" $ do
      do let t   = nil <+ uni "a" <+ exists "b"
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" ctx `shouldBe` Just (t <+ "a" := "Unit" <++ t')
      do let t   = nil 
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" ctx `shouldBe` Just (t <+ "a" := "Unit" <++ t')
      do let t   = nil <+ uni "a" <+ exists "b"
         let t'  = nil 
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" ctx `shouldBe` Just (t <+ "a" := "Unit" <++ t')
         
  describe "insertAt'" $ do
    it "fails with context without elem" $ do
      let ctx = nil <+ uni "a" <+ exists "b"
      let p = nil <+ uni "p"
      insertAt' (exists "a") p ctx `shouldBe` Nothing

    it "succeds in context with elem" $ do
      let ctx = nil <+ marker "m" <+ exists "a" <+ uni "a"
      let p = nil <+ uni "p"
      insertAt' (exists "a") p ctx `shouldBe` Just (nil <+ marker "m" <++ p <+ uni "a")

  describe "subtypeOf" $ do
    it "is reflexive" $ do
      runSubtypeOf0 @() "a"   "a" `shouldYield`   emptyCtx
      runSubtypeOf0 @() "a"   "a" `shouldYield`   emptyCtx
      do let ctx = nil <+ exists "a"
         runSubtypeOf ctx (E.exists "a") (E.exists "a") `shouldYield` ctx
         shouldFail $ runSubtypeOf nil (E.exists "a") (E.exists "a") 
      do let t  = "Nat" @->: "Nat"
         let t' = "Nat" @->: "Bool"
         runSubtypeOf nil t t `shouldYield` nil
         shouldFail $ runSubtypeOf nil t t' 
      do let t  = E.forAll ["a"] "Bool"
         let t' = E.forAll ["a"] "Nat"
         let t'' = E.forAll ["b"] "Bool"
         runSubtypeOf nil t t `shouldYield` nil
         shouldFail $ runSubtypeOf nil t t' 
         runSubtypeOf nil t t'' `shouldYield` nil

    it "foralls are alpha equivalent" $ do
      do let t  = E.forAll ["a"] "a"
         let t' = E.forAll ["b"] "b"
         runSubtypeOf nil t t' `shouldYield` nil
      do let t  = E.forAll ["a", "b"] ("a" @->: "b")
         let t' = E.forAll ["x", "y"] ("x" @->: "y")
         runSubtypeOf nil t t' `shouldYield` nil
      do let t  = E.forAll ["a", "b"] ("a" @->: "b" @->: "a")
         let t' = E.forAll ["x", "y"] ("x" @->: "y" @->: "x")
         runSubtypeOf nil t t' `shouldYield` nil

    it "universal variables are subtypes of everything" $ do
      do let t  = E.forAll ["a"] "a"
         let t' = ("x" @->: "y" @->: "x")
         runSubtypeOf nil t t' `shouldYield` nil
      do let t  = E.forAll ["a"] "a"
         let t' = "Nat"
         runSubtypeOf nil t t' `shouldYield` nil

    it "works with example from paper (1 -> forall alpha. alpha <: 1 -> 1)" $ do
      do let t  = "Unit" @->: E.forAll ["a"] "a"
         let t' = "Unit" @->: "Unit"
         runSubtypeOf nil t t' `shouldYield` nil
  
  describe "check" $ do

    it "checks primitives" $ do
      runCheck0 (E.nat 10) "Nat" `shouldYield` nil
      runCheck0 E.unit "Unit" `shouldYield` nil
      runCheck0 E.true "Bool" `shouldYield` nil
      runCheck0 E.true (E.forAll ["a"] "Bool") `shouldYield` nil
      shouldFail $ runCheck0 E.true (E.forAll ["a"] "Nat")
    
    it "checks variables" $ do
      let ctx = nil <+ "x" .: "Nat"
      runCheck ctx "x" "Nat" `shouldYield` ctx

    it "checks lambdas with mono-types" $ do
      runCheck0 ("x" @-> "x") ("Nat" @->: "Nat") `shouldYield` nil
      shouldFail $ runCheck0 ("x" @-> "y") ("Nat" @->: "Nat") 
      runCheck0 ("x" @-> "y" @-> "x") ("Nat" @->: "Bool" @->: "Nat") `shouldYield` nil
      shouldFail $ runCheck0 ("x" @-> "y" @-> "x") ("Nat" @->: "Bool" @->: "Bool") 
      runCheck0 ("x" @-> "y" @-> E.true) ("Nat" @->: "Nat" @->: "Bool") `shouldYield` nil
      shouldFail $ runCheck0 ("x" @-> "x" :: E.Expr ()) ("Nat") 
      do let ctx = nil <+ "x" .: "Nat"
         runCheck ctx ("y" @-> "x") ("Bool" @->: "Nat") `shouldYield` ctx

    it "checks lambdas with poly-types" $ do
      runCheck0 ("x" @-> "x") (E.forAll ["a"] $ "a" @->: "a") `shouldYield` nil
      runCheck0 ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "a") @->: (E.forAll ["b"] "a")) `shouldYield` nil
      runCheck0 ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "a") @->: "a") `shouldYield` nil
      runCheck0 ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "b") @->: "a") `shouldYield` nil
      shouldFail $ runCheck0 [unsafeExpr|\x -> x|] [unsafeType|forall a b. (forall c. b) -> a|]
      do let ctx = nil <+ "x" .: "Nat"
         runCheck ctx ("y" @-> "x") (E.forAll ["a"] $ "a" @->: "Nat") `shouldYield` ctx
    
    it "checks applications (mono)" $ do
      do let ctx = nil <+ "x" .: ("Nat" @->: "Nat")
         runCheck ctx ("x" @@ E.nat 10) "Nat" `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
         runCheck ctx ("x" @@ E.nat 10) ("Bool" @->: "Nat") `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
         runCheck ctx ("x" @@ E.nat 10 @@ E.true) ("Nat") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         runCheck ctx ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         shouldFail $ runCheck ctx ("x" @@ ("y" @-> E.true)) ("Nat") 
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         shouldFail $ runCheck ctx ("x" @@ ("y" @-> "y")) ("Bool") 

    it "checks applications (poly)" $ do
      -- Hmm, here the context is polluted with "a" := "Nat". Olle's implementation
      -- does the same... I wonder if that is supposed to happen?
      -- Seems kinda wrong
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a")
         runCheck ctx ("id" @@ E.nat 10) "Nat" `shouldYield` (ctx <+ "a" := "Nat")
      -- do let ctx = nil <+ "x" .: (E.forAll ["a"] $ "a" @->: "a")
      --    runCheck ctx ("x" @@ E.true) "Bool" `shouldYield` ctx

      -- do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
      --    runCheck ctx ("x" @@ E.nat 10) ("Bool" @->: "Nat") `shouldYield` ctx
      -- do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
      --    runCheck ctx ("x" @@ E.nat 10 @@ E.true) ("Nat") `shouldYield` ctx
      -- do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
      --    runCheck ctx ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx


