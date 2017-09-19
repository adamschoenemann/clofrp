{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.PolySpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import CloTT.Pretty
import Data.String (fromString)

import qualified CloTT.AST.Parsed  as E
import           CloTT.Check.Poly
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import           CloTT.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Pretty 

-- import Fixtures


foo :: (forall a. a -> a) -> (forall b. b -> b)
foo f = f

foo' :: forall b. b -> b
foo' = foo id

shouldYield :: (Show a1, Pretty a1, Show a2, Eq a2) 
            => (Either a1 a2, t, TypingWrite a) -> a2 -> Expectation
shouldYield (res, st, tree) ctx = 
  case res of
    Right ctx' -> do 
      -- failure (showTree tree)
      ctx' `shouldBe` ctx
    Left err   -> failure $ (showW 80 . pretty $ err) ++ "\nProgress:\n" ++ showTree tree

shouldFail :: (Show a, Show b) => (Either a b, t1, t) -> Expectation
shouldFail (res, st, tree) = res `shouldSatisfy` isLeft

polySpec :: Spec
polySpec = do
  let nil = emptyCtx @()
  let (.:) = HasType
  
  describe "wfContext" $ do
    specify "nil is well-formed" $ do
      wfContext nil `shouldBe` True
    specify "nil <+ a is well-formed" $ do
      wfContext (nil <+ uni "a") `shouldBe` True
      wfContext (nil <+ exists "a") `shouldBe` True
    specify "nil <+ a := ty is well-formed" $ do
      wfContext (nil <+ "a" := "Unit") `shouldBe` True
    specify "nil <+ a : ty is well-formed" $ do
      wfContext (nil <+ "a" .: "Unit") `shouldBe` True
    specify "nil <+ a <+ x : a is well-formed" $ do
      wfContext (nil <+ uni "a" <+ "x" .: "a") `shouldBe` True
    specify "nil <+ ^a <+ x : ^a is well-formed" $ do
      wfContext (nil <+ exists "a" <+ "x" .: E.exists "a") `shouldBe` True
    specify "nil <+ ^a <+ ^b = ^a is well-formed" $ do
      wfContext (nil <+ exists "a" <+ "b" := E.exists "a") `shouldBe` True

    specify "nil <+ a <+ a is not well-formed" $ do
      wfContext (nil <+ exists "a" <+ exists "a") `shouldBe` False
      wfContext (nil <+ exists "a" <+ uni "a") `shouldBe` False
      wfContext (nil <+ uni "a" <+ exists "a") `shouldBe` False
      wfContext (nil <+ uni "a" <+ uni "a") `shouldBe` False
    specify "nil <+ a <+ a : ty is not well-formed" $ do
      wfContext (nil <+ exists "a" <+ "a" .: "Unit") `shouldBe` False
      wfContext (nil <+ uni "a" <+ "a" .: "Unit") `shouldBe` False
    specify "nil <+ ^a = ^b is not well-formed" $ do
      wfContext (nil <+ "a" := E.exists "b") `shouldBe` False
    specify "nil <+ ^a = b is not well-formed" $ do
      wfContext (nil <+ "a" := "b") `shouldBe` False

  describe "<++" $ do
    it "should work" $ do
      let ctx = nil <+ exists "a" <+ exists "b" <+ "a" := "Nat" <+ "b" := "Unit"
      let ctx' = nil <++ (nil <+ exists "a") <++ (nil <+ exists "b" <+ "a" := "Nat" <+ "b" := "Unit")
      ctx' `shouldBe` ctx

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
      -- do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
      --    let ctx = xs <+ uni "b"
      --    splitCtx' (uni "b") ctx `shouldBe` Just (xs, uni "b", emptyCtx)
      -- do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
      --    let ys = nil <+ uni "z" <+ exists "u" <+ marker "v"
      --    let ctx = xs <+ uni "b" <++ ys
      --    splitCtx' (uni "b") ctx `shouldBe` Just (xs, uni "b", ys)
      -- do let id' = "x" .: E.forAll ["a"] ("a" @->: "a")
      --    let ctx = nil <+ id' <+ exists "a"
      --    splitCtx' (exists "a") ctx `shouldBe` Just (nil <+ id', exists "a", nil)
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
      do let t   = nil <+ uni "d" <+ exists "b"
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" ctx `shouldBe` Just (t <+ "a" := "Unit" <++ t')
      do let t   = nil 
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" ctx `shouldBe` Just (t <+ "a" := "Unit" <++ t')
      do let t   = nil <+ uni "d" <+ exists "b"
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
  
  describe "substCtx'" $ do
    it "subst existentials with their solutions" $ do
      do let ctx = nil <+ "a" := "Nat"
         substCtx' ctx (E.exists "a") `shouldBe` Right "Nat"
      do let ctx = nil <+ "a" := "Nat"
         substCtx' ctx (E.exists "a" @->: E.exists "a") `shouldBe` Right ("Nat" @->: "Nat")

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
         let t' = ("Nat" @->: "Bool" @->: "Unit")
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
         runCheck ctx ("id" @@ E.nat 10) "Nat" `shouldYield` (ctx <+ E.mname 0 := "Nat")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         runCheck ctx ("foo" @@ E.nat 10) ("Nat" @->: "Nat") `shouldYield` (ctx <+ E.mname 0 := "Nat")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         runCheck ctx ("foo" @@ E.nat 10 @@ E.nat 9) ("Nat") `shouldYield` (ctx <+ E.mname 0 := "Nat")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         shouldFail $ runCheck ctx ("foo" @@ E.nat 10 @@ E.true) ("Bool") 
    
    it "succeeds when applying same function twice to same type param" $ do
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a") 
                <+ "foo" .: ("Nat" @->: "Nat" @->: "Unit")
         runCheck ctx ("foo" @@ ("id" @@ E.nat 10) @@ ("id" @@ E.nat 10)) ("Unit")
           `shouldYield` (ctx <+ E.mname 0 := "Nat" <+ E.mname 1 := "Nat")

    it "succeeds when applying same function twice to different type params" $ do
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a") 
                <+ "foo" .: ("Nat" @->: "Bool" @->: "Unit")
         runCheck ctx ("foo" @@ ("id" @@ E.nat 10) @@ ("id" @@ E.true)) ("Unit")
           `shouldYield` (ctx <+ E.mname 0 := "Nat" <+ E.mname 1 := "Bool")
    
    it "works with rank-2 types" $ do
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: "Unit") 
         runCheck ctx ("r2" @@ ("x" @-> "x")) ("Unit")
           `shouldYield` (ctx)
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: (E.forAll ["b"] $ "b" @->: "b")) 
         runCheck ctx ("r2" @@ ("x" @-> "x")) (E.forAll ["b"] $ "b" @->: "b")
           `shouldYield` (ctx)
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: (E.forAll ["b"] $ "b" @->: "b")) 
         runCheck ctx ("r2" @@ ("x" @-> "x")) (E.forAll ["a"] $ "a" @->: "a")
           `shouldYield` (ctx)
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: (E.forAll ["b"] $ "b" @->: "b")) 
         runCheck ctx ("r2" @@ ("x" @-> "x")) ("Nat" @->: "Nat")
           `shouldYield` (ctx)
    
    it "works with church-encoded lists" $ do
      do -- List a := forall r. (a -> r -> r) -> r -> r
         let clist r a = 
              let r' = fromString r
                  a' = fromString a
              in E.forAll [fromString r] $ (a' @->: r' @->: r') @->: r' @->: r' 
         -- nil = \k -> \z -> z
         runCheck nil ("k" @-> "z" @-> "z") (E.forAll ["a"] $ clist "r" "a") `shouldYield` nil
         -- cons = \x xs -> k z -> x
         runCheck nil ("x" @-> "xs" @-> "k" @-> "z" @-> ("k" @@ "x" @@ ("xs" @@ "k" @@ "z")))
                  (E.forAll ["a"] $ "a" @->: clist "r" "a" @->: clist "r" "a")
                  `shouldYield` nil
         -- append : List a -> List a -> List a
         -- append : clist a r -> clist a r -> clist a r
         let append   = "xs" @-> "ys" @-> "k" @-> "z" @-> "xs" @@ "k" @@ ("ys" @@ "k" @@ "z")
             appendty = E.forAll ["a"] $ clist "r" "a" @->: clist "r" "a" @->: clist "r" "a"
         runCheck nil append appendty `shouldYield` nil

         -- singleton
         let sing   = "x" @-> "k" @-> "z" @-> "k" @@ "x" @@ "z"
             singty = E.forAll ["a"] $ "a" @->: clist "r" "a"
         runCheck nil sing singty `shouldYield` nil
         -- map
         let map   = "f" @-> "xs" @-> "k" @-> "z" @-> ("xs" @@ ("x" @-> "k" @@ ("f" @@ "x")) @@ "z")
             mapty = E.forAll ["a", "b"] $ ("a" @->: "b") @->: clist "r" "a" @->: clist "r" "b"
         runCheck nil map mapty `shouldYield` nil
    
    it "checks id against (∃a -> ∃b)" $ do
      -- this results in wrong order of solved existentials
      runCheck (nil <+ exists "a" <+ exists "b") ("x" @-> "x") (E.exists "a" @->: E.exists "b")
        `shouldYield` (nil <+ exists "a" <+ ("b" := E.exists "a"))

    it "`apply id <= (∀a. a -> a)` when apply : ∀a b. (a -> b) -> a -> b" $ do
      let ctx = nil <+ "apply" .: (E.forAll ["a", "b"] $ ("a" @->: "b") @->: "a" @->: "b")
      runCheck ctx ("apply" @@ ("x" @-> "x")) (E.forAll ["a"] $ "a" @->: "a") `shouldYield` ctx

    it "`apply id x <= a` when apply : ∀a b. (a -> b) -> a -> b" $ do
      let ctx = nil <+ "apply" .: (E.forAll ["a", "b"] $ ("a" @->: "b") @->: "a" @->: "b")
      runCheck ctx ("apply" @@ ("x" @-> "x") @@ E.true) ("Bool") `shouldYield` (ctx <+ E.mname 0 := "Bool" <+ E.mname 1 := E.exists (E.mname 0))
    
    it "`r2 double` fails when r2 : (∀a. a) -> (), double : Nat -> Nat" $ do
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: "Unit") <+ "double" .: ("Nat" @->: "Nat")
         shouldFail $ runCheck ctx ("r2" @@ "double") ("Unit")
    
    -- it "works with type constructors" $ do
    --   do let ctx = nil <+ "xs" .: ("List" @@: "Nat") <+ "hd" .: (E.forAll ["a"] $ "List" @@: "a" @->: "a")
    --      runCheck ctx ("hd" @@ "xs") "Nat" `shouldYield` (ctx <+ E.mname 0 := "Nat")

    -- it "checks map applied to a list" $ do
    --   let map' = "map" .: (E.forAll ["a", "b"] $ ("a" @->: "b") @->: "List" @@: "a" @->: "List" @@: "b")
    --   let ctx = nil <+ "xs" .: ("List" @@: "Nat") <+ map'

    --   runCheck ctx ("map" @@ ("x" @-> "x") @@ "xs") ("List" @@: "Nat") `shouldYield` (ctx <+ E.mname 0 := "Nat")
      -- runCheck ctx ("map" @@ ("x" @-> E.true) @@ "xs") ("List" @@: "Bool") `shouldYield` (ctx <+ E.mname 0 := "Nat")

    -- it "works with runST" $ do
    --   let runST = "runST" .: (E.forAll ["a"] $ (E.forAll ["s"] $ "ST" @@: "s" @@: "a") @->: "a")
    --   let ctx = nil <+ "c" .: ("ST" @@: "s" @@: "Nat") <+ runST
    --   runCheck ctx ("runST" @@ "c") "Nat" `shouldYield` nil
           


      -- do let ctx = nil <+ "x" .: (E.forAll ["a"] $ "a" @->: "a")
      --    runCheck ctx ("x" @@ E.true) "Bool" `shouldYield` ctx

      -- do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
      --    runCheck ctx ("x" @@ E.nat 10) ("Bool" @->: "Nat") `shouldYield` ctx
      -- do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
      --    runCheck ctx ("x" @@ E.nat 10 @@ E.true) ("Nat") `shouldYield` ctx
      -- do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
      --    runCheck ctx ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx


