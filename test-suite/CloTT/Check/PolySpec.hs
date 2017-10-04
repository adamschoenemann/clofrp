{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}

module CloTT.Check.PolySpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import CloTT.Pretty
import Data.String (fromString)

import qualified CloTT.AST.Parsed  as E
import           CloTT.Check.Poly
import           CloTT.Check.Poly.Prog
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

bar :: (forall a. [a]) -> Int
bar xs = 
  case xs of
    [] -> 0
    (x:xs)  -> x

-- rank2 :: (forall a. [a]) -> Either () Bool
-- rank2 = \xs ->
--   case xs of
--     [] -> Left ()
--     [x] -> Left x
--     x:xs' -> Right x


shouldYield :: (Show a1, Pretty a1, Show a2, Eq a2) 
            => (Either a1 a2, t, TypingWrite a) -> a2 -> Expectation
shouldYield (res, st, tree) ctx = 
  case res of
    Right ctx' -> do 
      -- failure (showTree tree)
      ctx' `shouldBe` ctx
    Left err   -> do 
      failure $ showW 200 $ pretty err <> "\nProgress:\n" <> prettyTree tree

shouldFail :: (Show a, Show b) => (Either a b, t1, TypingWrite ann) -> Expectation
shouldFail (res, st, tree) = 
  case res of
    Left err -> True `shouldBe` True
    Right _  -> failure (showW 200 . prettyTree $ tree)

polySpec :: Spec
polySpec = do
  let nil = emptyCtx @()
  let rd fctx kctx ctx = TR ctx fctx kctx mempty
  let rd'  = rd mempty 
  let rd'' = rd mempty mempty
  let (.:) = HasType
  let stdkinds = 
        [ "Nat" |-> Star, "Unit" |-> Star, "Bool" |-> Star, "Int" |-> Star
        , "List" |-> Star :->*: Star, "Maybe" |-> Star :->*: Star
        ]

  describe "inferVarKind" $ do
    it "should work for just the variable" $ do
      inferVarKind @() mempty "a" ("a") `shouldBe` Right Star
    it "should work for a -> a" $ do
      inferVarKind @() mempty "a" ("a" @->: "a") `shouldBe` Right Star
    it "should work for a -> Int" $ do
      inferVarKind ["Int" |-> Star] "a" ("a" @->: "Int") `shouldBe` Right Star
    it "fail for just Int" $ do
      inferVarKind @() ["Int" |-> Star] "a" "Int" `shouldSatisfy` isLeft
    it "should work for a Int" $ do
      inferVarKind ["Int" |-> Star] "a" ("a" @@: "Int") `shouldBe` Right (Star :->*: Star)
    it "should work for List a" $ do
      inferVarKind ["List" |-> (Star :->*: Star)] "a" ("List" @@: "a") `shouldBe` Right Star
    it "should work for List (List a)" $ do
      inferVarKind ["List" |-> (Star :->*: Star)] "a" ("List" @@: ("List" @@: "a")) `shouldBe` Right Star
    it "should work for a List" $ do
      inferVarKind ["List" |-> (Star :->*: Star)] "a" ("a" @@: "List") `shouldBe` Right ((Star :->*: Star) :->*: Star)
    it "should work for a List Int" $ do
      pending
      -- inferVarKind ["Int" |-> Star, "List" |-> (Star :->*: Star)] "a" ("a" @@: "List" @@: "Int")
      --   `shouldBe` Right ((Star :->*: Star) :->*: Star :->*: Star)
  
  describe "wfContext" $ do
    specify "nil is well-formed" $ do
      wfContext mempty nil `shouldBe` True
    specify "nil <+ a is well-formed" $ do
      wfContext mempty (nil <+ uni "a") `shouldBe` True
      wfContext mempty (nil <+ exists "a") `shouldBe` True
    specify "nil <+ a := ty is well-formed" $ do
      wfContext stdkinds (nil <+ "a" := "Unit") `shouldBe` True
      wfContext mempty (nil <+ "a" := "Unit") `shouldBe` False
    specify "nil <+ a : ty is well-formed" $ do
      wfContext stdkinds (nil <+ "a" .: "Unit") `shouldBe` True
      wfContext mempty (nil <+ "a" .: "Unit") `shouldBe` False
    specify "nil <+ a <+ x : a is well-formed" $ do
      wfContext mempty (nil <+ uni "a" <+ "x" .: "a") `shouldBe` True
    specify "nil <+ ^a <+ x : ^a is well-formed" $ do
      wfContext mempty (nil <+ exists "a" <+ "x" .: E.exists "a") `shouldBe` True
    specify "nil <+ ^a <+ ^b = ^a is well-formed" $ do
      wfContext mempty (nil <+ exists "a" <+ "b" := E.exists "a") `shouldBe` True
    specify "`nil <+ ^a <+ ^b = Either Unit <+ ^c = ∃b ∃a` is well-formed" $ do
      let Just cass = E.asMonotype (E.exists "b" @@: E.exists "a")
      let Just eapp = E.asMonotype ("Either" @@: "Unit")
      let kctx = ["Unit" |-> Star, "Either" |-> Star :->*: Star :->*: Star]
      wfContext kctx (nil <+ exists "a" <+ "b" := eapp <+ "c" := cass) `shouldBe` True

    specify "nil <+ a <+ a is not well-formed" $ do
      wfContext mempty (nil <+ exists "a" <+ exists "a") `shouldBe` False
      wfContext mempty (nil <+ exists "a" <+ uni "a") `shouldBe` False
      wfContext mempty (nil <+ uni "a" <+ exists "a") `shouldBe` False
      wfContext mempty (nil <+ uni "a" <+ uni "a") `shouldBe` False
    specify "nil <+ a <+ a : ty is not well-formed" $ do
      wfContext mempty (nil <+ exists "a" <+ "a" .: "Unit") `shouldBe` False
      wfContext mempty (nil <+ uni "a" <+ "a" .: "Unit") `shouldBe` False
    specify "nil <+ ^a = ^b is not well-formed" $ do
      wfContext mempty (nil <+ "a" := E.exists "b") `shouldBe` False
    specify "nil <+ ^a = b is not well-formed" $ do
      wfContext mempty (nil <+ "a" := "b") `shouldBe` False

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
      before' (exists "a") (exists "b") ctx `shouldBe` True
    it "before' a b (.,b,a) == False" $ do
      let ctx = nil <+ exists "b" <+ exists "a"
      before' (exists "a") (exists "b") ctx `shouldBe` False
    it "before' a b (.,b,T,a) == False" $ do
      let t   = nil <+ uni "x" <+ exists "y"
      let ctx = nil <+ exists "b" <++ t <+ exists "a"
      before' (exists "a") (exists "b") ctx `shouldBe` False

  describe "assign'" $ do
    let kctx = ["Unit" |-> Star]
    it "fails for empty context" $ do
      let ctx = nil
      assign' "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "fails for singleton context without 'a^'" $ do
      let ctx = nil <+ exists "b"
      assign' "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "fails for singleton context without 'a^' but with 'a'" $ do
      let ctx = nil <+ uni "a"
      assign' "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "fails for context without 'a^' but with 'a'" $ do
      let ctx = nil <+ uni "a" <+ exists "b" <+ marker "c"
      assign' "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "works for context with 'a^'" $ do
      do let t   = nil <+ uni "d" <+ exists "b"
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" kctx ctx `shouldBe` Right (t <+ "a" := "Unit" <++ t')
      do let t   = nil 
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" kctx ctx `shouldBe` Right (t <+ "a" := "Unit" <++ t')
      do let t   = nil <+ uni "d" <+ exists "b"
         let t'  = nil 
         let ctx = t <+ exists "a" <++ t'
         assign' "a" "Unit" kctx ctx `shouldBe` Right (t <+ "a" := "Unit" <++ t')
         
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
    it "substs existentials with their solutions" $ do
      do let ctx = nil <+ "a" := "Nat"
         substCtx' ctx (E.exists "a") `shouldBe` Right "Nat"
      do let ctx = nil <+ "a" := "Nat"
         substCtx' ctx (E.exists "a" @->: E.exists "a") `shouldBe` Right ("Nat" @->: "Nat")
    it "substitutes simultaneously" $ do
      let ctx = nil <+ exists "c" <+ "b" := E.exists "c" <+ "a" := E.exists "b"
      substCtx' ctx (E.exists "a") `shouldBe` Right (E.exists "c")

  -- TODO: Add tests with type constructors
  describe "subtypeOf" $ do
    it "is reflexive" $ do
      let mk = rd' ["Nat" |-> Star, "Bool" |-> Star]
      do let ctx = nil <+ uni "a"
         runSubtypeOf (rd'' ctx) "a" "a" `shouldYield` ctx
         shouldFail $ runSubtypeOf (rd'' nil) "Nat" "Nat" 
         runSubtypeOf (mk nil) "Nat" "Nat" `shouldYield` nil
      do let ctx = nil <+ exists "a"
         runSubtypeOf (rd'' ctx) (E.exists "a") (E.exists "a") `shouldYield` ctx
         shouldFail $ runSubtypeOf (rd'' nil) (E.exists "a") (E.exists "a") 
      do let t  = "Nat" @->: "Nat"
         let t' = "Nat" @->: "Bool"
         shouldFail $ runSubtypeOf (mk nil) t t' 
      do let t  = E.forAll ["a"] "Bool"
         let t' = E.forAll ["a"] "Nat"
         let t'' = E.forAll ["b"] "Bool"
         let ctx = mk nil
         runSubtypeOf ctx t t `shouldYield` nil
         shouldFail $ runSubtypeOf ctx t t' 
         runSubtypeOf ctx t t'' `shouldYield` nil

    it "foralls are alpha equivalent" $ do
      do let t  = E.forAll ["a"] "a"
         let t' = E.forAll ["b"] "b"
         runSubtypeOf (rd'' nil) t t' `shouldYield` nil
      do let t  = E.forAll ["a", "b"] ("a" @->: "b")
         let t' = E.forAll ["x", "y"] ("x" @->: "y")
         runSubtypeOf (rd'' nil) t t' `shouldYield` nil
      do let t  = E.forAll ["a", "b"] ("a" @->: "b" @->: "a")
         let t' = E.forAll ["x", "y"] ("x" @->: "y" @->: "x")
         runSubtypeOf (rd'' nil) t t' `shouldYield` nil

    it "universal variables are subtypes of everything" $ do
      do let t  = E.forAll ["a"] "a"
         let t' = ("Nat" @->: "Bool" @->: "Unit")
         let ctx = rd' ["Nat" |-> Star, "Bool" |-> Star, "Unit" |-> Star] nil
         runSubtypeOf ctx t t' `shouldYield` nil
      do let t  = E.forAll ["a"] "a"
         let t' = "Nat"
         let ctx = rd' ["Nat" |-> Star] nil
         runSubtypeOf ctx t t' `shouldYield` nil

    it "works with example from paper (1 -> forall alpha. alpha <: 1 -> 1)" $ do
      do let t  = "Unit" @->: E.forAll ["a"] "a"
         let t' = "Unit" @->: "Unit"
         let ctx = rd' ["Unit" |-> Star] nil
         runSubtypeOf ctx t t' `shouldYield` nil
    
    specify "applied type-constructors are subtypes (1)" $ do
      let lctx = nil <+ uni "b"
      let ctx = rd' ["Maybe" |-> Star :->*: Star] lctx
      runSubtypeOf ctx (E.forAll ["a"] "a") ("Maybe" @@: "b") `shouldYield` lctx

    specify "applied type-constructors are subtypes (2)" $ do
      let lctx = nil
      let ctx = rd' ["Maybe" |-> Star :->*: Star, "Unit" |-> Star] lctx
      runSubtypeOf ctx (E.forAll ["a"] $ "Maybe" @@: "a") ("Maybe" @@: "Unit") `shouldYield` lctx

  describe "synthesize" $ do
    
    it "synthesizes primitives" $ do
      runSynth (rd'' nil) (E.nat 10) `shouldYield` ("Nat",  nil)
      runSynth (rd'' nil) (E.true)   `shouldYield` ("Bool", nil)
      runSynth (rd'' nil) (E.false)  `shouldYield` ("Bool", nil)
      runSynth (rd'' nil) (E.unit)   `shouldYield` ("Unit", nil)
    
    it "synthesizes variables" $ do
      let tctx = nil <+ "x" .: "Nat"
      runSynth (rd' ["Nat" |-> Star] tctx) "x" `shouldYield` ("Nat", tctx)

    it "synthesizes annotated expressions" $ do
      let mk = rd' ["Nat" |-> Star, "Bool" |-> Star]
      do let tctx = nil <+ "x" .: "Nat"
         runSynth (mk tctx) (E.the "Nat" "x") `shouldYield` ("Nat", tctx)
      runSynth (mk nil) (E.the "Nat" (E.nat 10)) `shouldYield` ("Nat", nil)
      shouldFail $ runSynth (mk nil) (E.the "Bool" (E.nat 10))
      runSynth (mk nil) (E.the "Bool" (E.true)) `shouldYield` ("Bool", nil)
      runSynth (mk nil) (E.the ("Bool" @->: "Nat") ("x" @-> E.nat 10)) `shouldYield` ("Bool" @->: "Nat", nil)
      shouldFail $ runSynth (mk nil) (E.the ("Bool" @->: "Nat") ("x" @-> "x")) 
      runSynth (mk nil) (E.the ("Bool" @->: "Bool") ("x" @-> "x")) `shouldYield` ("Bool" @->: "Bool", nil)
      shouldFail $ runSynth (mk nil) (E.the (E.forAll ["a"] "Bool" @->: "a") ("x" @-> "x")) 

      do let t = E.forAll ["a"] $ "a" @->: "Bool"
         runSynth (mk nil) (E.the t ("x" @-> E.true)) `shouldYield` (t, nil)

      do let ctx = rd ["id" |-> E.forAll ["a"] ("a" @->: "a")] ["Nat" |-> Star] nil
         runSynth ctx (E.the ("Nat" @->: "Nat") "id") `shouldYield` ("Nat" @->: "Nat", nil)

  describe "check" $ do

    it "checks primitives" $ do
      let ctx = rd' ["Nat" |-> Star, "Bool" |-> Star, "Unit" |-> Star] nil
      runCheck ctx (E.nat 10) "Nat" `shouldYield` nil
      runCheck ctx E.unit "Unit" `shouldYield` nil
      runCheck ctx E.true "Bool" `shouldYield` nil
      runCheck ctx E.true (E.forAll ["a"] "Bool") `shouldYield` nil
      shouldFail $ runCheck ctx E.true (E.forAll ["a"] "Nat")
    
    it "checks variables" $ do
      do let tctx = nil <+ "x" .: "Nat"
         let ctx = rd' ["Nat" |-> Star] tctx
         runCheck ctx "x" "Nat" `shouldYield` tctx
      do let tctx = nil
         let ctx = rd ["x" |-> "Nat"] ["Nat" |-> Star] tctx
         runCheck ctx "x" "Nat" `shouldYield` tctx
      do let tctx = nil
         let ctx = rd ["foo" |-> "Nat" @->: "Nat", "x" |-> "Nat"] ["Nat" |-> Star] tctx
         runCheck ctx ("foo" @@ "x") "Nat" `shouldYield` tctx

    it "checks lambdas with mono-types" $ do
      do let ctx = rd' ["Nat" |-> Star, "Bool" |-> Star] nil
         runCheck ctx ("x" @-> "x") ("Nat" @->: "Nat") `shouldYield` nil
         shouldFail $ runCheck ctx ("x" @-> "y") ("Nat" @->: "Nat") 
         runCheck ctx ("x" @-> "y" @-> "x") ("Nat" @->: "Bool" @->: "Nat") `shouldYield` nil
         shouldFail $ runCheck ctx ("x" @-> "y" @-> "x") ("Nat" @->: "Bool" @->: "Bool") 
         runCheck ctx ("x" @-> "y" @-> E.true) ("Nat" @->: "Nat" @->: "Bool") `shouldYield` nil
         shouldFail $ runCheck ctx ("x" @-> "x" :: E.Expr ()) ("Nat") 
      do let ctx = nil <+ "x" .: "Nat"
         runCheck (rd' ["Nat" |-> Star] ctx) ("y" @-> "x") ("Bool" @->: "Nat") `shouldYield` ctx

    it "checks lambdas with poly-types" $ do
      do let ctx = rd'' nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ "a" @->: "a") `shouldYield` nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "a") @->: (E.forAll ["b"] "a")) `shouldYield` nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "a") @->: "a") `shouldYield` nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "b") @->: "a") `shouldYield` nil
         shouldFail $ runCheck (rd'' emptyCtx) [unsafeExpr|\x -> x|] [unsafeType|forall a b. (forall c. b) -> a|]
      do let ctx = nil <+ "x" .: "Nat"
         runCheck (rd' ["Nat" |-> Star] ctx) ("y" @-> "x") (E.forAll ["a"] $ "a" @->: "Nat") `shouldYield` ctx
    
    it "checks applications (mono)" $ do
      let mk = rd' ["Nat" |-> Star, "Bool" |-> Star]
      do let ctx = nil <+ "x" .: ("Nat" @->: "Nat")
         runCheck (mk ctx) ("x" @@ E.nat 10) "Nat" `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
         runCheck (mk ctx) ("x" @@ E.nat 10) ("Bool" @->: "Nat") `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
         runCheck (mk ctx) ("x" @@ E.nat 10 @@ E.true) ("Nat") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         runCheck (mk ctx) ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         shouldFail $ runCheck (mk ctx) ("x" @@ ("y" @-> E.true)) ("Nat") 
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         shouldFail $ runCheck (mk ctx) ("x" @@ ("y" @-> "y")) ("Bool") 

    it "checks applications (poly)" $ do
      -- Hmm, here the context is polluted with "a" := "Nat". Olle's implementation
      -- does the same... I wonder if that is supposed to happen?
      -- Seems kinda wrong
      let mk = rd' ["Nat" |-> Star, "Bool" |-> Star]
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a")
         runCheck (mk ctx) ("id" @@ E.nat 10) "Nat" `shouldYield` (ctx <+ E.mname 0 := "Nat")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         runCheck (mk ctx) ("foo" @@ E.nat 10) ("Nat" @->: "Nat") `shouldYield` (ctx <+ E.mname 0 := "Nat")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         runCheck (mk ctx) ("foo" @@ E.nat 10 @@ E.nat 9) ("Nat") `shouldYield` (ctx <+ E.mname 0 := "Nat")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         shouldFail $ runCheck (mk ctx) ("foo" @@ E.nat 10 @@ E.true) ("Bool") 
    
    it "succeeds when applying same function twice to same type param" $ do
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a") 
                <+ "foo" .: ("Nat" @->: "Nat" @->: "Unit")
         runCheck (rd' ["Nat" |-> Star, "Unit" |-> Star] ctx) ("foo" @@ ("id" @@ E.nat 10) @@ ("id" @@ E.nat 10)) ("Unit")
           `shouldYield` (ctx <+ E.mname 0 := "Nat" <+ E.mname 1 := "Nat")

    it "succeeds when applying same function twice to different type params" $ do
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a") 
                <+ "foo" .: ("Nat" @->: "Bool" @->: "Unit")
         runCheck (rd' ["Nat" |-> Star, "Bool" |-> Star, "Unit" |-> Star] ctx)
                  ("foo" @@ ("id" @@ E.nat 10) @@ ("id" @@ E.true))
                  ("Unit")
           `shouldYield` (ctx <+ E.mname 0 := "Nat" <+ E.mname 1 := "Bool")
    
    it "works with type-constructors (1)" $ do
      let lctx = nil 
      let kctx = ["Maybe" |-> Star :->*: Star, "Nat" |-> Star]
      let fctx = ["Just" |-> E.forAll ["a"] ("a" @->: "Maybe" @@: "a")]
      let ctx = rd fctx kctx lctx
      runCheck ctx ("Just" @@ E.nat 10) ("Maybe" @@: "Nat") `shouldYield` (lctx <+ E.mname 0 := "Nat")

    it "works with type-constructors (2)" $ do
      let lctx = nil 
      let kctx = ["Maybe" |-> Star :->*: Star, "Nat" |-> Star]
      let fctx = ["Just" |-> E.forAll ["a"] ("a" @->: "Maybe" @@: "a")]
      let ctx = rd fctx kctx lctx
      runCheck ctx ("Just" @@ E.nat 10) ("Maybe" @@: "Nat") `shouldYield` (lctx <+ E.mname 0 := "Nat")

    it "fails Just 10 <= forall a. Maybe a" $ do
      let lctx = nil 
      let kctx = ["Maybe" |-> Star :->*: Star, "Nat" |-> Star]
      let fctx = ["Just" |-> E.forAll ["a"] ("a" @->: "Maybe" @@: "a")]
      let ctx = rd fctx kctx lctx
      shouldFail $ runCheck ctx ("Just" @@ E.nat 10) (E.forAll ["a"] $ "Maybe" @@: "a")
    
    it "works with rank-2 types" $ do
      let mk = rd' ["Unit" |-> Star, "Nat" |-> Star]
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: "Unit") 
         runCheck (mk ctx) ("r2" @@ ("x" @-> "x")) ("Unit")
           `shouldYield` (ctx)
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: (E.forAll ["b"] $ "b" @->: "b")) 
         runCheck (mk ctx) ("r2" @@ ("x" @-> "x")) (E.forAll ["b"] $ "b" @->: "b")
           `shouldYield` (ctx)
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: (E.forAll ["b"] $ "b" @->: "b")) 
         runCheck (mk ctx) ("r2" @@ ("x" @-> "x")) (E.forAll ["a"] $ "a" @->: "a")
           `shouldYield` (ctx)
      do let ctx = nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: (E.forAll ["b"] $ "b" @->: "b")) 
         runCheck (mk ctx) ("r2" @@ ("x" @-> "x")) ("Nat" @->: "Nat")
           `shouldYield` (ctx)
    
    it "works with church-encoded lists" $ do
      do -- clist a := forall r. (a -> r -> r) -> r -> r
         let mk = rd''
         let clist a = 
              let r' = fromString "r"
                  a' = fromString a
              in E.forAll [fromString "r"] $ (a' @->: r' @->: r') @->: r' @->: r' 
         -- nil = \k -> \z -> z
         runCheck (mk nil) ("k" @-> "z" @-> "z") (E.forAll ["a"] $ clist "a") `shouldYield` nil
         -- cons = \x xs -> k z -> x
         runCheck (mk nil) ("x" @-> "xs" @-> "k" @-> "z" @-> ("k" @@ "x" @@ ("xs" @@ "k" @@ "z")))
                  (E.forAll ["a"] $ "a" @->: clist "a" @->: clist "a")
                  `shouldYield` nil
         -- append : forall a. clist a -> clist a -> clist a
         let append   = "xs" @-> "ys" @-> "k" @-> "z" @-> "xs" @@ "k" @@ ("ys" @@ "k" @@ "z")
             appendty = E.forAll ["a"] $ clist "a" @->: clist "a" @->: clist "a"
         runCheck (mk nil) append appendty `shouldYield` nil

         -- singleton
         let sing   = "x" @-> "k" @-> "z" @-> "k" @@ "x" @@ "z"
             singty = E.forAll ["a"] $ "a" @->: clist "a"
         runCheck (mk nil) sing singty `shouldYield` nil
         -- map
         let cmap   = "f" @-> "xs" @-> "k" @-> "z" @-> ("xs" @@ ("x" @-> "k" @@ ("f" @@ "x")) @@ "z")
             cmapty = E.forAll ["a", "b"] $ ("a" @->: "b") @->: clist "a" @->: clist "b"
         runCheck (mk nil) cmap cmapty `shouldYield` nil
    
    it "checks id against (∃a -> ∃b)" $ do
      -- this results in wrong order of solved existentials
      runCheck (rd'' $ nil <+ exists "a" <+ exists "b") ("x" @-> "x") (E.exists "a" @->: E.exists "b")
        `shouldYield` (nil <+ exists "a" <+ ("b" := E.exists "a"))

    it "`apply id <= (∀a. a -> a)` when apply : ∀a b. (a -> b) -> a -> b" $ do
      let ctx = nil <+ "apply" .: (E.forAll ["a", "b"] $ ("a" @->: "b") @->: "a" @->: "b")
      runCheck (rd'' ctx) ("apply" @@ ("x" @-> "x")) (E.forAll ["a"] $ "a" @->: "a") `shouldYield` ctx

    it "`apply id x <= a` when apply : ∀a b. (a -> b) -> a -> b" $ do
      let ctx = nil <+ "apply" .: (E.forAll ["a", "b"] $ ("a" @->: "b") @->: "a" @->: "b")
      runCheck (rd' ["Bool" |-> Star] ctx)
               ("apply" @@ ("x" @-> "x") @@ E.true) ("Bool")
               `shouldYield` (ctx <+ E.mname 0 := "Bool" <+ E.mname 1 := E.exists (E.mname 0))
    
    it "`r2 double` fails when r2 : (∀a. a) -> (), double : Nat -> Nat" $ do
      do let ctx =  nil <+ "r2" .: ((E.forAll ["a"] $ "a" @->: "a") @->: "Unit") <+ "double" .: ("Nat" @->: "Nat")
         shouldFail $ runCheck (rd' ["Unit" |-> Star] ctx) ("r2" @@ "double") ("Unit")
    
    it "works with type constructors" $ do
      do let ctx = nil <+ "xs" .: ("List" @@: "Nat") <+ "hd" .: (E.forAll ["a"] $ "List" @@: "a" @->: "a")
         runCheck (rd' ["Nat" |-> Star, "List" |-> Star :->*: Star] ctx) ("hd" @@ "xs") "Nat" `shouldYield` (ctx <+ E.mname 0 := "Nat")

    it "checks map applied to a list" $ do
      let map' = "map" .: (E.forAll ["a", "b"] $ ("a" @->: "b") @->: "List" @@: "a" @->: "List" @@: "b")
      let ctx = nil <+ "xs" .: ("List" @@: "Nat") <+ map'
      let ctx' = rd' ["Nat" |-> Star, "Bool" |-> Star, "List" |-> Star :->*: Star] ctx
      runCheck ctx' ("map" @@ ("x" @-> "x") @@ "xs") ("List" @@: "Nat") `shouldYield` (ctx <+ E.mname 0 := "Nat" <+ E.mname 1 := E.exists (E.mname 0))
      runCheck ctx' ("map" @@ ("x" @-> E.true) @@ "xs") ("List" @@: "Bool") `shouldYield` (ctx <+ E.mname 0 := "Nat" <+ E.mname 1 := "Bool")

    it "works with runST" $ do
      let runST = "runST" .: (E.forAll ["a"] $ (E.forAll ["s"] $ "ST" @@: "s" @@: "a") @->: "a")
      let ctx = nil <+ "c" .: (E.forAll ["s"] $ "ST" @@: "s" @@: "Nat") <+ runST
      runCheck (rd' ["Nat" |-> Star, "ST" |-> Star :->*: Star :->*: Star] ctx)
               ("runST" @@ "c") "Nat"
               `shouldYield` (ctx <+ E.mname 0 := "Nat")
           
    it "works with some lambdas and stuff" $ do
      let mk = rd' ["Bool" |-> Star, "Nat" |-> Star]
      do let ctx = nil <+ "x" .: (E.forAll ["a"] $ "a" @->: "a")
         runCheck (mk ctx) ("x" @@ E.true) "Bool" `shouldYield` (ctx <+ E.mname 0 := "Bool")
      do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
         runCheck (mk ctx) ("x" @@ E.nat 10) ("Bool" @->: "Nat") `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Nat" @->: "Bool" @->: "Nat")
         runCheck (mk ctx) ("x" @@ E.nat 10 @@ E.true) ("Nat") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Nat" @->: "Bool") @->: "Bool")
         runCheck (mk ctx) ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx

  describe "kindOf'" $ do
    let kinds = [ ("List"  |-> Star :->*: Star)
                , ("Tuple" |-> Star :->*: Star :->*: Star)
                , ("Nat"   |-> Star)
                , ("a"     |-> Star)
                , ("b"     |-> Star)
                ]
    -- let [listK, tupK, natK, aK, bK] = kinds

    it "looks up kinds" $ do
      kindOf' kinds "Nat" `shouldBe` Right Star

    it "infers arrow types to be kind *" $ do
      kindOf' kinds ("Nat" @->: "Nat") `shouldBe` Right Star
      kindOf' kinds ("List" @@: "Nat" @->: "List" @@: "Nat") `shouldBe` Right Star

    it "fails when type not found in ctx" $ do
      kindOf' @() [] "Nat" `shouldSatisfy` isLeft
    
    it "fails with partially applied types in arrows" $ do
      kindOf' kinds ("List" @->: "a") `shouldSatisfy` isLeft

    it "infers lists" $ do
      kindOf' kinds ("List" @@: "a") `shouldBe` Right Star

    it "infers tuples (curried)" $ do
      kindOf' kinds ("Tuple" @@: "a") `shouldBe` Right (Star :->*: Star)

    it "infers tuples" $ do
      kindOf' kinds ("Tuple" @@: "a" @@: "b") `shouldBe` Right Star

    it "infers tuples of lists" $ do
      kindOf' kinds ("Tuple" @@: ("List" @@: "a") @@: "b") `shouldBe` Right Star

    it "infers foralls" $ do
      kindOf' kinds (E.forAll ["a"] $ "List" @@: "a") `shouldBe` Right Star
      kindOf' kinds  (E.forAll ["a", "b"] $ "Tuple" @@: "a" @@: "b") `shouldBe` Right Star
      kindOf' kinds  (E.forAll ["a"] "a" @->: E.forAll ["a"] "a") `shouldBe` Right Star
      kindOf' kinds  (E.forAll ["a"] "List" @@: "a" @->: "a") `shouldBe` Right Star

  describe "checkProg" $ do
    it "fails programs with invalid types (1)" $ do
      let prog = [unsafeProg|
        data Foo a = MkFoo a.
        foo : Foo -> Nat.
        foo = \x -> x.
      |]
      shouldFail $ runCheckProg mempty prog

    it "succeeds for mono-types" $ do
      let prog = [unsafeProg|
        data Int = .
        data IntList = Nil | Cons Int IntList.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "fails programs with invalid types (2)" $ do
      let prog = [unsafeProg|
        data List a = Nil | Cons a (List a a).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails programs with invalid types (3)" $ do
      let prog = [unsafeProg|
        data List = Nil | Cons a (List a).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "succeeds for some simple functions" $ do
      let prog = [unsafeProg|
        data Unit = Unit.
        foo : Unit -> Unit.
        foo = \x -> x.
        app : (Unit -> Unit) -> Unit -> Unit.
        app = \f -> \x -> f x.
        bar : Unit.
        bar = app foo Unit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for some simple poly functions" $ do
      let prog = [unsafeProg|
        foo : forall a. a -> a.
        foo = \x -> x.
        app : forall a b. (a -> b) -> a -> b.
        app = \f -> \x -> f x.
        data Unit = Unit.
        bar : Unit.
        bar = app foo Unit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for monomorphic patterns (1)" $ do
      let prog = [unsafeProg|
        data FooBar = Foo | Bar.
        data Two = One | Two.
        foo : FooBar -> Two.
        foo = \x ->
          case x of
            | Foo -> One
            | Bar -> Two.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for monomorphic patterns (2)" $ do
      let prog = [unsafeProg|
        data FooBar = Foo | Bar.
        data Two = One FooBar | Two.
        foo : FooBar -> Two.
        foo = \x ->
          case x of
            | Foo -> One x
            | Bar -> Two.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "suceeds for polymorphic patterns (1)" $ do
      let prog = [unsafeProg|
        data Maybe a = Nothing | Just a.
        data Int = .
        data FooBar = Foo Int | Bar.
        m1 : forall a. Maybe a.
        m1 = Nothing.

        isFoo : FooBar -> Maybe Int.
        isFoo = \x ->
          case x of
            | Foo i -> Just i
            | Bar -> Nothing.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "suceeds for simple poly pattern match (Wrap)" $ do
      let prog = [unsafeProg|
        data Wrap t = MkWrap t.
        unWrap : forall a. Wrap a -> a.
        unWrap = \x ->
          case x of
            | MkWrap x' -> x'.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "suceeds for nested poly pattern match (Wrap)" $ do
      let prog = [unsafeProg|
        data Wrap t = MkWrap t.
        unUnWrap : forall a. Wrap (Wrap a) -> a.
        unUnWrap = \x ->
          case x of
            | MkWrap (MkWrap x') -> x'.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for not-deep-enough pattern matches" $ do
      let prog = [unsafeProg|
        data Wrap t = MkWrap t.
        unUnWrap : forall a. Wrap (Wrap a) -> a.
        unUnWrap = \x ->
          case x of
            | MkWrap x' -> x'.
      |]
      shouldFail $ runCheckProg mempty prog

    it "succeeds for nested list matching" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Maybe a = Nothing | Just a.
        head2 : forall a. List a -> Maybe a.
        head2 = \xs -> 
          case xs of
            | Cons x (Cons x' xs') -> Just x'.
            | xs' -> Nothing
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for lists and and maybe" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        singleton : forall a. a -> List a.
        singleton = \x -> Cons x Nil.

        data Maybe a = Nothing | Just a.
        head : forall a. List a -> Maybe a.
        head = \xs -> 
          case xs of
            | Nil -> Nothing
            | Cons x xs' -> Just x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for rank2 crap" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Unit = MkUnit.
        foo : (forall a. List a) -> Unit.
        foo = \xs ->
          case xs of
            | Nil -> MkUnit
            | Cons x xs -> x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for rank2 crap" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Unit = MkUnit.
        data Either a b = Left a | Right b.
        data Bool = True | False.
        foo : (forall a. List a) -> Either Unit Bool.
        foo = \xs ->
          case xs of
            | Cons x Nil -> Left x
            | Cons x Nil -> Right x.
      |]
      -- runCheckProg mempty prog `shouldYield` ()
      shouldFail $ runCheckProg mempty prog 

    it "suceeds for rank2 stuff" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Pair a b = Pair a b.
        data Bool = True | False.
        data Unit = Unit.
        foo : (forall a. a -> a) -> Pair (List Bool) (Unit).
        foo = \id ->
          Pair (Cons (id True) Nil) (id Unit).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for tricky polymorphism (1)" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).

        data Maybe a = Nothing | Just a.
        head : forall a b. List a -> Maybe b.
        head = \xs -> 
          case xs of
            | Nil -> Nothing
            | Cons x xs' -> Just x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails getRight" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        getRight : forall a b. Either a b -> b.
        getRight = \e ->
          case e of
            | Left x -> x
            | Right x -> x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for tricky polymorphism (2)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall a b. Either a b -> Maybe a.
        toMaybe = \e ->
          case e of
            | Left x -> Nothing
            | Right x -> Just x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for wrong patterns" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall a b. Either a b -> Maybe a.
        toMaybe = \e ->
          case e of
            | Left x -> Nothing
            | Just x -> Just x.
      |]
      shouldFail $ runCheckProg mempty prog 
    
    it "fails for impredicative types" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall b. Either (forall a. a) b -> b.
        toMaybe = \e ->
          case e of
            | Left x -> x
            | Just x -> x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "succeeds for toMaybe" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall a b. Either a b -> Maybe b.
        toMaybe = \e ->
          case e of
            | Left x -> Nothing
            | Right x -> Just x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "suceeds for polymorphic function composition" $ do
      let prog = [unsafeProg|

        compose : forall a b c. (b -> c) -> (a -> b) -> (a -> c).
        compose = \g -> \f -> \x -> g (f x).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "infers the type of lambdas" $ do
      let prog = [unsafeProg|

        data Bool = True | False.
        data Unit = MkUnit.
        test : Bool -> Unit.
        test = \x -> (\x' -> MkUnit) x.

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "suceeds for contravariant functor" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Predicate a = Pred (a -> Bool).

        comap : forall a b. (b -> a) -> Predicate a -> Predicate b.
        comap = \fn -> \pred -> 
          case pred of
            | Pred fn' -> Pred (\x -> fn' (fn x)).
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for lefts" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Either a b = Left a | Right b.
        data List a = Nil | Cons a (List a).

        lefts : forall a b. List (Either a b) -> List a.
        lefts = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Left x) xs'  -> Cons x (lefts xs')
            | Cons (Right x) xs' -> lefts xs'.

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for incorrect rights" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Either a b = Left a | Right b.
        data List a = Nil | Cons a (List a).

        rights : forall a b. List (Either a b) -> List b.
        rights = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Left x) xs'  -> Cons x (rights xs')
            | Cons (Right x) xs' -> rights xs'.
      |]
      shouldFail $ runCheckProg mempty prog

    -- we need a new rule to instantiate existentials with type-applications
    it "succeeds for a bunch of eithers" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Unit = MkUnit.
        data A = MkA.
        data B = MkB.

        either1 : Either (Either Unit Unit) Unit.
        either1 = Left (Left MkUnit).
        either2 : Either (Either B A) A.
        either2 = Left (Right MkA).
        either3 : Either (Either B A) A.
        either3 = Left (Left MkB).
        either4 : Either (Either B A) A.
        either4 = Right MkA.
      |]
      runCheckProg mempty prog `shouldYield` ()


    it "succeeds for a bunch of polymorphic eithers" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.

        either1 : forall a b c. a -> Either a (Either b c).
        either1 = \a -> Left a.
        either2 : forall a. a -> Either a (Either a a).
        either2 = \a -> Left a.
        either3 : forall a b c. a -> Either (Either a b) c.
        either3 = \a -> Left (Left a).
        either4 : forall a b c. b -> Either (Either a b) c.
        either4 = \a -> Left (Right a).
        either5 : forall a b c d. b -> Either (Either a b) (Either c d).
        either5 = \a -> Left (Right a).
        either6 : forall a b c d e. b -> Either (Either a (Either b c)) (Either d e).
        either6 = \a -> Left (Right (Left a)).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for nested eithers (either-swap)" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Either a b = Left a | Right b.

        main : forall a b c d. Either (Either a b) (Either c d) -> Either (Either d c) (Either b a).
        main = \e1 ->
          case e1 of
            | Left  (Left  a) -> Right (Left a)
            | Left  (Right b) -> Right (Right b)
            | Right (Left  c) -> Left  (Right c)
            | Right (Right d) -> Left  (Left d).
      |]
      shouldFail $ runCheckProg mempty prog

    it "fails for a bunch of eithers (1)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data A = MkA.
        data B = MkB.

        either : Either (Either B A) A.
        either = Left (Left MkA).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for a bunch of eithers (2)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data A = MkA.
        data B = MkB.

        either : Either A (Either B A).
        either = Right (Left MkA).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for a bunch of eithers (3)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.

        either : forall a b c. a -> Either a (Either b c).
        either = \x -> Right (Left x).
      |]
      shouldFail $ runCheckProg mempty prog 
    
    it "suceeds for church lists" $ do
      let prog = [unsafeProg|
        data ChurchList a = ChurchList (forall r. (a -> r -> r) -> r -> r).
        data List a = Nil | Cons a (List a).
        
        runList : forall a. ChurchList a -> forall r. (a -> r -> r) -> r -> r.
        runList = \cl ->
          case cl of
            | ChurchList fn -> fn.
        
        -- | Make a 'ChurchList' out of a regular list.
        -- fromList : forall a. List a -> ChurchList a.
        -- fromList xs = ChurchList (\k -> \z -> foldr k z xs
        
        -- | Turn a 'ChurchList' into a regular list.
        toList : forall a. ChurchList a -> List a.
        toList = \xs -> runList xs Cons Nil.
        
        -- | The 'ChurchList' counterpart to '(:)'.  Unlike 'DList', whose
        -- implementation uses the regular list type, 'ChurchList' abstracts
        -- over it as well.
        cons : forall a. a -> ChurchList a -> ChurchList a.
        cons = \x -> \xs -> ChurchList (\k -> \z -> k x (runList xs k z)).
        
        -- | Append two 'ChurchList's.  This runs in O(1) time.  Note that
        -- there is no need to materialize the lists as @[a]@.
        append : forall a. ChurchList a -> ChurchList a -> ChurchList a.
        append = \xs -> \ys -> ChurchList (\k -> \z -> runList xs k (runList ys k z)).
        
        -- i.e.,
        
        nil : forall a. ChurchList a.
        nil = ChurchList (\k -> \z -> z).
        
        singleton : forall a. a -> ChurchList a.
        singleton = \x -> ChurList (\k -> \z -> k x z).

        snoc : forall a. ChurchList a -> a -> ChurchList a.
        snoc = \xs -> \x -> ChurchList (\k z -> runList xs k (k x z)).
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for Data.Either stdlib" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data List a = Nil | Cons a (List a).
        data Bool = True | False.
        data Pair a b = MkPair a b.

        either : forall a b c. (a -> c) -> (b -> c) -> Either a b -> c.
        either = \lf -> \rf -> \e ->
          case e of
            | Left l -> lf l
            | Right r -> rf r.
        
        lefts : forall a b. List (Either a b) -> List a.
        lefts = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Left x) xs'  -> Cons x (lefts xs')
            | Cons (Right x) xs' -> lefts xs'.

        rights : forall a b. List (Either a b) -> List b.
        rights = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Right x) xs' -> Cons x (rights xs')
            | Cons (Left x) xs'  -> rights xs'.
        
        partitionEithers : forall a b. List (Either a b) -> Pair (List a) (List b).
        partitionEithers = \xs ->
          case xs of
            | Nil -> MkPair Nil Nil
            | Cons x xs' -> 
              case (partitionEithers xs') of
                | MkPair ls rs ->
                  case x of
                    | Left x' -> MkPair (Cons x' ls) rs
                    | Right x' -> MkPair ls (Cons x' rs).
        
        isLeft : forall a b. Either a b -> Bool.
        isLeft = \e ->
          case e of
            | Left x -> True
            | Right x -> False.

        isRight : forall a b. Either a b -> Bool.
        isRight = \e ->
          case e of
            | Left x -> False
            | Right x -> True.
        
        fromLeft : forall a b. a -> Either a b -> a.
        fromLeft = \d -> \e ->
          case e of
            | Left x -> x
            | Right x -> d.

        fromRight : forall a b. b -> Either a b -> b.
        fromRight = \d -> \e ->
          case e of
            | Left x -> d
            | Right x -> x.
        
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for superfluous quantifiers" $ do
      let prog = [unsafeProg|
        foo : forall a b c. a -> a.
        foo = \x -> x.

        data Unit = MkUnit.
        bar : Unit.
        bar = foo MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for impossible defs" $ do
      let prog = [unsafeProg|
        foo : forall a b. a -> b.
        foo = \x -> x.
      |]
      shouldFail $ runCheckProg mempty prog 
    
    it "succeeds for non-regular data (omg)" $ do
      let prog = [unsafeProg|
        data Pair a = MkPair a a.
        data BalTree a = Empty | Branch a (BalTree (Pair a)).
        data Nat = Z | S Nat.

        zero : Nat.
        zero = Z.
        one : Nat.
        one = S zero.
        two : Nat.
        two = S one.
        three : Nat.
        three = S two.

        ex01 : forall a. BalTree a.
        ex01 = Empty.

        ex02 : BalTree Nat.
        ex02 = Branch zero Empty.

        ex03 : BalTree Nat.
        ex03 = Branch zero (Branch (MkPair one two) Empty).

        ex04 : BalTree Nat.
        ex04 =
          Branch
            zero 
            (Branch
              (MkPair one two)
              (Branch
                (MkPair (MkPair three three) (MkPair three three))
                Empty
              )
             ).
        
        ofDepth : forall a. a -> Nat -> BalTree a.
        ofDepth = \x -> \n ->
          case n of
            | Z -> Empty
            | S n' -> Branch x (ofDepth (MkPair x x) n').

      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for higher-kinded types" $ do
      let prog = [unsafeProg|
        data Functor f = Functor (forall a b. (a -> b) -> f a -> f b) .
      |]
      pending
      -- runCheckProg mempty prog `shouldYield` ()


