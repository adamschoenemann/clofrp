{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}

module CloFRP.CheckSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.String (fromString)

import qualified CloFRP.AST  as E
import           CloFRP.Check
import           CloFRP.Check.Prog
import qualified Data.Map.Strict as M
import           CloFRP.AST ((@->:), (@@:), Kind(..))
import           CloFRP.AST (LamCalc(..))
import           CloFRP.QuasiQuoter
import           CloFRP.Check.TestUtils
import           CloFRP.TestUtils
import           CloFRP.Pretty
import           CloFRP.Annotated 
import           CloFRP.Utils

foo :: (forall a. a -> a) -> (forall b. b -> b)
foo f = f

foo' :: forall b. b -> b
foo' = foo id

bar :: (forall a. [a]) -> Int
bar xs = 
  case xs of
    [] -> 0
    (x:xs')  -> x

-- rank2 :: (forall a. [a]) -> Either () Bool
-- rank2 = \xs ->
--   case xs of
--     [] -> Left ()
--     [x] -> Left x
--     x:xs' -> Right x



typecheckSpec :: Spec
typecheckSpec = do
  let nil = mempty :: LocalCtx ()
  let stdlib = ["True" |-> A mempty (E.TFree "Bool"), "False" |-> A mempty (E.TFree "Bool")]
  let rd fctx kctx ctx = TR ctx (fctx `mappend` stdlib) kctx mempty mempty 
  let rd'  = rd mempty 
  let rd'' = rd mempty mempty
  let stdkinds = 
        [ "Nat" |-> Star, "Unit" |-> Star, "Bool" |-> Star, "Int" |-> Star
        , "List" |-> Star :->*: Star, "Maybe" |-> Star :->*: Star
        ]

  let als = M.fromList 
  let al x b e = (x, E.Synonym x (map (,Star) b) e)
  let errs e x = (unann (fst x)) `shouldBe` e

  describe "mustBeStableUnder" $ do
    let runmsu c k = runTypingM0 (c `mustBeStableUnder` k) mempty
    specify "nil is stable under all k's" $ do
      runmsu nil "k" `shouldYield` ()
    specify "nil <+ a is stable under all k's" $ do
      runmsu (nil <+ exists "a") "k" `shouldYield` ()
    specify "nil <+ k is stable under all k's" $ do
      runmsu (nil <+ exists "k") "k" `shouldYield` ()
    specify "nil <+ x : Nat -> Nat is stable under all k's" $ do
      runmsu (nil <+ "k" <\: ("Nat" @->: "Nat")) "k" `shouldYield` ()
    specify "nil <+ x : |>k' Nat is stable under all k's" $ do
      runmsu (nil <+ "k" <\: E.later "k'" "Nat") "k" `shouldYield` ()
    specify "nil <+ x λ: |>k Nat is not stable under all k's" $ do
      runmsu (nil <+ "x" <\: E.later "k" "Nat") "k" `shouldFailWith` (errs $ Other "Context not stable wrt k due to x λ: ⊳k Nat")
    specify "nil <+ x : |>k Nat *is* stable under all k's" $ do
      runmsu (nil <+ "x" .: E.later "k" "Nat") "k" `shouldYield` ()

  
  describe "checkRecSynonymes" $ do
    let checkAl x = runTypingM0 @() (checkRecSynonymes x) mempty
    it "rejects recursive type synonyms" $ do
      checkAl [al "Foo" [] "Foo"]                             `shouldFailWith` errs (Other "Foo is recursive")
      checkAl [al "Foo" ["a"] $ "Foo" @@: "a"]                `shouldFailWith` errs (Other "Foo is recursive")
      checkAl [al "Units" [] $ "Pair" @@: "Unit" @@: "Units"] `shouldFailWith` errs (Other "Units is recursive")

    it "rejects mutually recursive type synonyms" $ do
      shouldFailWith (checkAl [al "Bar" [] "Foo", al "Foo" [] $ "Unit" @->: "Bar"]) (errs $ Other "Bar is recursive")
      shouldFailWith (checkAl [al "Foo" [] $ "Unit" @->: "Bar", al "Bar" [] $ "Id" @@: "Foo", al "Id" ["a"] "a"]) (errs $ Other "Bar is recursive")

  describe "deBruijnify" $ do
    it "does nothing with no bound vars" $ do
      deBruijnify () [] ("Either" @@: "a" @@: "b") `shouldBe` ("Either" @@: "a" @@: "b")
    it "works as expected" $ do
      deBruijnify () ["a"] ("Either" @@: "a" @@: "b") `shouldBe` ("Either" @@: (E.debrjn 0) @@: "b")
      deBruijnify () ["a", "b"] ("Either" @@: "a" @@: "b") `shouldBe` ("Either" @@: (E.debrjn 0) @@: (E.debrjn 1))
      deBruijnify () ["a", "b", "c"] ("a" @@: ("b" @@: "c")) `shouldBe` (E.debrjn 0 @@: (E.debrjn 1 @@: E.debrjn 2))
      deBruijnify () ["a"] ("a" @@: ("a" @@: "a")) `shouldBe` (E.debrjn 0 @@: (E.debrjn 0 @@: E.debrjn 0))

  describe "synonymExpansion" $ do
    it "should work with flipsum" $ do
      let (Ex _ f) = synonymExpansion () (E.Synonym "FlipSum" [("a", Star), ("b", Star)] $ "Either" @@: "b" @@: "a")
      let (Ex _ f') = f ("a")
      f' "b" `shouldBe` Done ("Either" @@: "b" @@: "a")

    it "should work with nested flipsum" $ do
      let (Ex _ f1) = synonymExpansion () (E.Synonym "FlipSum" [("a", Star), ("b", Star)] $ "Either" @@: "b" @@: "a")
      let (Ex _ f2) = f1 ("a")
      let (Done t) = f2 ("FlipSum" @@: "b" @@: "d")
      t `shouldBe` ("Either" @@: ("FlipSum" @@: "b" @@: "d") @@: "a")

  describe "expandSynonymes" $ do
    let shouldExpandTo e1 e2 =
          case runTypingM0 e1 mempty of
            (Right e2', _, _) -> e2' `shouldBe` e2
            (Left e, _, _)    -> failure (pps e)

    it "expands the simplest of synonyms" $ do
      expandSynonymes @() (als [al "Foo" [] "Bar"]) "Foo" `shouldExpandTo` "Bar"
      expandSynonymes @() (als [al "Foo" [] "Bar"]) ("Foo" @->: "Foo") `shouldExpandTo` ("Bar" @->: "Bar")
      expandSynonymes @() (als [al "Foo" [] "Bar"]) (E.forAll ["a"] $ "a" @->: "Foo") `shouldExpandTo` (E.forAll ["a"] $ "a" @->: "Bar")
      -- below should actually fail, but I guess the "kind-check" should catch it instead?
      expandSynonymes @() (als [al "Foo" [] "Bar"]) ("Foo" @@: "a" @->: "Foo") `shouldExpandTo` ("Bar" @@: "a" @->: "Bar")

    it "expands synonyms with one param" $ do
      expandSynonymes @() (als [al "Id" ["a"] "a"]) ("Id" @@: "a") `shouldExpandTo` ("a")
      expandSynonymes @() (als [al "Id" ["a"] "a"]) ("Id" @@: "Foo") `shouldExpandTo` ("Foo")
      expandSynonymes @() (als [al "Id" ["a"] "a"]) ("Id" @@: ("Id" @@: "Foo")) `shouldExpandTo` ("Foo")
      expandSynonymes @() (als [al "Id" ["a"] "a"]) ("Id" @@: "a" @->: "Id" @@: "b") `shouldExpandTo` ("a" @->: "b")
      expandSynonymes @() (als [al "Option" ["a"] $ "Maybe" @@: "a"]) ("List" @@: ("Option" @@: "a") @->: "Option" @@: ("List" @@: "a"))
        `shouldExpandTo` ("List" @@: ("Maybe" @@: "a") @->: "Maybe" @@: ("List" @@: "a"))
      expandSynonymes @() (als [al "Option" ["a"] $ "Maybe" @@: "a"]) ("Option" @@: ("Option" @@: "a"))
        `shouldExpandTo` ("Maybe" @@: ("Maybe" @@: "a"))

    it "expands synonyms with two params" $ do
      expandSynonymes @() (als [al "FlipSum" ["a", "b"] $ "Either" @@: "b" @@: "a"]) 
                        ("FlipSum" @@: "a" @@: "b") 
        `shouldExpandTo` ("Either" @@: "b" @@: "a")
    
    it "avoids name capture problems" $ do
      do let synonyms = als [al "FlipSum" ["a", "b"] $ "Either" @@: "b" @@: "a"]
         expandSynonymes @() synonyms ("FlipSum" @@: "a" @@: ("FlipSum" @@: "b" @@: "c")) 
           `shouldExpandTo` ("Either" @@: ("Either" @@: "c" @@: "b") @@: "a")
      do let synonyms = als [al "FlipSum" ["a", "b"] $ "Either" @@: "b" @@: "a"]
         expandSynonymes @() synonyms ("FlipSum" @@: ("FlipSum" @@: "a" @@: "b") @@: "c") 
          `shouldExpandTo` ("Either" @@: "c" @@: ("Either" @@: "b" @@: "a"))
      do let synonyms = als [al "App" ["a", "b", "c"] $ "a" @@: "b" @@: "c"]
         expandSynonymes @() synonyms ("App" @@: "c" @@: "c" @@: "a") 
          `shouldExpandTo` ("c" @@: "c" @@: "a")
    
    it "fails partial applications" $ do
      let assertPartial x = case runTypingM0 x mempty of
            (Left (PartialSynonymApp _, _), _, _) -> success
            (e, _, _)                           -> failure (show e) 

      -- TODO: Fix this
      do let synonyms = als [al "Arr" ["a", "b"] $ "a" @->: "b"]
         assertPartial $ expandSynonymes @() synonyms ("Arr" @@: "Int")
      -- do let synonyms = als [al "Id" ["a"] "a", al "Arr" ["a", "b"] $ "a" @->: "b"]
      --    assertPartial $ expandSynonymes @() synonyms ("Id" @@: ("Arr" @@: "Int"))


  -- NOTE: Work in progress (for higher-kinded types)
  -- describe "inferVarKind" $ do
  --   it "should work for just the variable" $ do
  --     inferVarKind @() mempty "a" ("a") `shouldBe` Right Star
  --   it "should work for a -> a" $ do
  --     inferVarKind @() mempty "a" ("a" @->: "a") `shouldBe` Right Star
  --   it "should work for a -> Int" $ do
  --     inferVarKind ["Int" |-> Star] "a" ("a" @->: "Int") `shouldBe` Right Star
  --   it "fail for just Int" $ do
  --     inferVarKind @() ["Int" |-> Star] "a" "Int" `shouldSatisfy` isLeft
  --   it "should work for a Int" $ do
  --     inferVarKind ["Int" |-> Star] "a" ("a" @@: "Int") `shouldBe` Right (Star :->*: Star)
  --   it "should work for List a" $ do
  --     inferVarKind ["List" |-> (Star :->*: Star)] "a" ("List" @@: "a") `shouldBe` Right Star
  --   it "should work for List (List a)" $ do
  --     inferVarKind ["List" |-> (Star :->*: Star)] "a" ("List" @@: ("List" @@: "a")) `shouldBe` Right Star
  --   it "should work for a List" $ do
  --     inferVarKind ["List" |-> (Star :->*: Star)] "a" ("a" @@: "List") `shouldBe` Right ((Star :->*: Star) :->*: Star)
  --   -- it "should work for a List Int" $ do
  --   --   pending
  --     -- inferVarKind ["Int" |-> Star, "List" |-> (Star :->*: Star)] "a" ("a" @@: "List" @@: "Int")
  --     --   `shouldBe` Right ((Star :->*: Star) :->*: Star :->*: Star)
  
  describe "wfContext" $ do
    let runWfContext ks ctx = 
          runTypingM0 (wfContext ctx) (mempty {trKinds = ks, trCtx = ctx})

    specify "nil is well-formed" $ do
      runWfContext mempty nil `shouldYield` ()
    specify "nil <+ a is well-formed" $ do
      runWfContext mempty (nil <+ uni "a") `shouldYield` ()
      runWfContext mempty (nil <+ exists "a") `shouldYield` ()
    specify "nil <+ a := ty is well-formed" $ do
      runWfContext stdkinds (nil <+ "a" := "Unit") `shouldYield` ()
      shouldFail $ runWfContext mempty (nil <+ "a" := "Unit")
    specify "nil <+ a : ty is well-formed" $ do
      runWfContext stdkinds (nil <+ "a" .: "Unit") `shouldYield` ()
      shouldFail $ runWfContext mempty (nil <+ "a" .: "Unit")
    specify "nil <+ a <+ x : a is well-formed" $ do
      runWfContext mempty (nil <+ uni "a" <+ "x" .: "a") `shouldYield` ()
    specify "nil <+ ^a <+ x : ^a is well-formed" $ do
      runWfContext mempty (nil <+ exists "a" <+ "x" .: E.exists "a") `shouldYield` ()
    specify "nil <+ ^a <+ ^b = ^a is well-formed" $ do
      runWfContext mempty (nil <+ exists "a" <+ "b" := E.exists "a") `shouldYield` ()
    specify "`nil <+ ^a <+ ^b = Either Unit <+ ^c = ∃b ∃a` is well-formed" $ do
      let Just cass = E.asMonotype (E.exists "b" @@: E.exists "a")
      let Just eapp = E.asMonotype ("Either" @@: "Unit")
      let kctx = ["Unit" |-> Star, "Either" |-> Star :->*: Star :->*: Star]
      runWfContext kctx (nil <+ exists "a" <+ "b" := eapp <+ "c" := cass) `shouldYield` ()

    specify "nil <+ a <+ a is not well-formed" $ do
      shouldFail $ runWfContext mempty (nil <+ exists "a" <+ exists "a")
      shouldFail $ runWfContext mempty (nil <+ exists "a" <+ uni "a")
      shouldFail $ runWfContext mempty (nil <+ uni "a" <+ exists "a")
      shouldFail $ runWfContext mempty (nil <+ uni "a" <+ uni "a")
    specify "nil <+ a <+ a : ty is not well-formed" $ do
      shouldFail $ runWfContext mempty (nil <+ exists "a" <+ "a" .: "Unit")
      shouldFail $ runWfContext mempty (nil <+ uni "a" <+ "a" .: "Unit")
    specify "nil <+ ^a = ^b is not well-formed" $ do
      shouldFail $ runWfContext mempty (nil <+ "a" := E.exists "b")
    specify "nil <+ ^a = b is not well-formed" $ do
      shouldFail $ runWfContext mempty (nil <+ "a" := "b")

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
         splitCtx' (uni "b") ctx `shouldBe` Just (mempty, uni "b", mempty)
      do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
         let ctx = nil <+ uni "b" <++ xs
         splitCtx' (uni "b") ctx `shouldBe` Just (mempty, uni "b", xs)
      do let xs = nil <+ uni "x" <+ exists "y" <+ marker "x"
         let ctx = xs <+ uni "b"
         splitCtx' (uni "b") ctx `shouldBe` Just (xs, uni "b", mempty)
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
      let ctx = LocalCtx @() []
      before' (exists "a") (exists "b") ctx `shouldBe` False
    it "fails on singleton context" $ do
      let ctx = LocalCtx @() [exists "a"]
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

  describe "assign" $ do
    let kctx = ["Unit" |-> Star]
    let runAssign nm ty ks cs = 
          let (r, _, _) = runTypingM0 (assign nm ty) (mempty {trKinds = ks, trCtx = cs})
          in  r
    it "fails for empty context" $ do
      let ctx = nil
      runAssign "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "fails for singleton context without 'a^'" $ do
      let ctx = nil <+ exists "b"
      runAssign "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "fails for singleton context without 'a^' but with 'a'" $ do
      let ctx = nil <+ uni "a"
      runAssign "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "fails for context without 'a^' but with 'a'" $ do
      let ctx = nil <+ uni "a" <+ exists "b" <+ marker "c"
      runAssign "a" "Unit" kctx ctx `shouldSatisfy` isLeft

    it "works for context with 'a^'" $ do
      do let t   = nil <+ uni "d" <+ exists "b"
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         runAssign "a" "Unit" kctx ctx `shouldBe` Right (t <+ "a" := "Unit" <++ t')
      do let t   = nil 
         let t'  = nil <+ marker "c"
         let ctx = t <+ exists "a" <++ t'
         runAssign "a" "Unit" kctx ctx `shouldBe` Right (t <+ "a" := "Unit" <++ t')
      do let t   = nil <+ uni "d" <+ exists "b"
         let t'  = nil 
         let ctx = t <+ exists "a" <++ t'
         runAssign "a" "Unit" kctx ctx `shouldBe` Right (t <+ "a" := "Unit" <++ t')
         
  describe "insertAt'" $ do
    it "fails with context without elem" $ do
      let ctx = nil <+ uni "a" <+ exists "b"
      let p = nil <+ uni "p"
      insertAt' (exists "a") p ctx `shouldBe` Nothing

    it "succeds in context with elem" $ do
      let ctx = nil <+ marker "m" <+ exists "a" <+ uni "a"
      let p = nil <+ uni "p"
      insertAt' (exists "a") p ctx `shouldBe` Just (nil <+ marker "m" <++ p <+ uni "a")
  
  describe "substCtx" $ do
    let runSubstCtx ctx ty = runTypingM0 (substCtx ctx ty) mempty
    it "substs existentials with their solutions" $ do
      do let ctx = nil <+ "a" := "Nat"
         runSubstCtx ctx (E.exists "a") `shouldYield` "Nat"
      do let ctx = nil <+ "a" := "Nat"
         runSubstCtx ctx (E.exists "a" @->: E.exists "a") `shouldYield` ("Nat" @->: "Nat")
    it "substitutes simultaneously" $ do
      let ctx = nil <+ exists "c" <+ "b" := E.exists "c" <+ "a" := E.exists "b"
      runSubstCtx ctx (E.exists "a") `shouldYield` (E.exists "c")

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
      runSynth (rd'' nil) (E.int 10) `shouldYield` ("Int",  nil)
      runSynth (rd'' nil) (E.unit)   `shouldYield` ("Unit", nil)
    
    it "synthesizes variables" $ do
      let tctx = nil <+ "x" .: "Nat"
      runSynth (rd' ["Nat" |-> Star] tctx) "x" `shouldYield` ("Nat", tctx)

    it "synthesizes annotated expressions" $ do
      let mk = rd' ["Nat" |-> Star, "Bool" |-> Star]
      do let tctx = nil <+ "x" .: "Nat"
         runSynth (mk tctx) (E.the "Nat" "x") `shouldYield` ("Nat", tctx)
      runSynth (mk nil) (E.the "Int" (E.int 10)) `shouldYield` ("Int", nil)
      shouldFail $ runSynth (mk nil) (E.the "Bool" (E.int 10))
      runSynth (mk nil) (E.the "Bool" (E.true)) `shouldYield` ("Bool", nil)
      runSynth (mk nil) (E.the ("Bool" @->: "Int") ("x" @-> E.int 10)) `shouldYield` ("Bool" @->: "Int", nil)
      shouldFail $ runSynth (mk nil) (E.the ("Bool" @->: "Nat") ("x" @-> "x")) 
      runSynth (mk nil) (E.the ("Bool" @->: "Bool") ("x" @-> "x")) `shouldYield` ("Bool" @->: "Bool", nil)
      shouldFail $ runSynth (mk nil) (E.the (E.forAll ["a"] "Bool" @->: "a") ("x" @-> "x")) 

      do let t = E.forAll ["a"] $ "a" @->: "Bool"
         runSynth (mk nil) (E.the t ("x" @-> E.true)) `shouldYield` (t, nil)

      do let ctx = rd ["id" |-> E.forAll ["a"] ("a" @->: "a")] ["Nat" |-> Star] nil
         runSynth ctx (E.the ("Nat" @->: "Nat") "id") `shouldYield` ("Nat" @->: "Nat", nil)

  describe "check" $ do

    it "checks primitives" $ do
      let ctx = rd' ["Bool" |-> Star, "Unit" |-> Star] nil
      runCheck ctx (E.int 10) "Int" `shouldYield` nil
      runCheck ctx E.unit "Unit" `shouldYield` nil
      runCheck ctx E.true "Bool" `shouldYield` nil
      runCheck ctx E.true (E.forAll ["a"] "Bool") `shouldYield` nil
      shouldFail $ runCheck ctx E.true (E.forAll ["a"] "Int")
    
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
         runCheck (rd' ["Nat" |-> Star, "Bool" |-> Star] ctx) ("y" @-> "x") ("Bool" @->: "Nat") `shouldYield` ctx

    it "checks lambdas with poly-types" $ do
      do let ctx = rd'' nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ "a" @->: "a") `shouldYield` nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "a") @->: (E.forAll ["b"] "a")) `shouldYield` nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "a") @->: "a") `shouldYield` nil
         runCheck ctx ("x" @-> "x") (E.forAll ["a"] $ (E.forAll ["b"] "b") @->: "a") `shouldYield` nil
         shouldFail $ runCheck (rd'' mempty) ("x" @-> "x") (E.forAll ["a", "b"] $ (E.forAll ["c"] "b") @->: "a")
      do let ctx = nil <+ "x" .: "Nat"
         runCheck (rd' ["Nat" |-> Star] ctx) ("y" @-> "x") (E.forAll ["a"] $ "a" @->: "Nat") `shouldYield` ctx
    
    it "checks applications (mono)" $ do
      let mk = rd' ["Bool" |-> Star]
      do let ctx = nil <+ "x" .: ("Int" @->: "Int")
         runCheck (mk ctx) ("x" @@ E.int 10) "Int" `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Int" @->: "Bool" @->: "Int")
         runCheck (mk ctx) ("x" @@ E.int 10) ("Bool" @->: "Int") `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Int" @->: "Bool" @->: "Int")
         runCheck (mk ctx) ("x" @@ E.int 10 @@ E.true) ("Int") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Int" @->: "Bool") @->: "Bool")
         runCheck (mk ctx) ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Int" @->: "Bool") @->: "Bool")
         shouldFail $ runCheck (mk ctx) ("x" @@ ("y" @-> E.true)) ("Int") 
      do let ctx = nil <+ "x" .: (("Int" @->: "Bool") @->: "Bool")
         shouldFail $ runCheck (mk ctx) ("x" @@ ("y" @-> "y")) ("Bool") 

    it "checks applications (poly)" $ do
      -- Hmm, here the context is polluted with "a" := "Int". Olle's implementation
      -- does the same... I wonder if that is supposed to happen?
      -- Seems kinda wrong
      let mk = rd' ["Bool" |-> Star]
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a")
         runCheck (mk ctx) ("id" @@ E.int 10) "Int" `shouldYield` (ctx <+ E.mname 0 := "Int")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         runCheck (mk ctx) ("foo" @@ E.int 10) ("Int" @->: "Int") `shouldYield` (ctx <+ E.mname 0 := "Int")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         runCheck (mk ctx) ("foo" @@ E.int 10 @@ E.int 9) ("Int") `shouldYield` (ctx <+ E.mname 0 := "Int")
      do let ctx = nil <+ "foo" .: (E.forAll ["a"] $ "a" @->: "a" @->: "a")
         shouldFail $ runCheck (mk ctx) ("foo" @@ E.int 10 @@ E.true) ("Bool") 
    
    it "succeeds when applying same function twice to same type param" $ do
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a") 
                <+ "foo" .: ("Int" @->: "Int" @->: "Unit")
         runCheck (rd' ["Unit" |-> Star] ctx) ("foo" @@ ("id" @@ E.int 10) @@ ("id" @@ E.int 10)) ("Unit")
           `shouldYield` (ctx <+ E.mname 0 := "Int" <+ E.mname 1 := "Int")

    it "succeeds when applying same function twice to different type params" $ do
      do let ctx = nil <+ "id" .: (E.forAll ["a"] $ "a" @->: "a") 
                <+ "foo" .: ("Int" @->: "Bool" @->: "Unit")
         runCheck (rd' ["Bool" |-> Star, "Unit" |-> Star] ctx)
                  ("foo" @@ ("id" @@ E.int 10) @@ ("id" @@ E.true))
                  ("Unit")
           `shouldYield` (ctx <+ E.mname 0 := "Int" <+ E.mname 1 := "Bool")
    
    it "works with type-constructors (1)" $ do
      let lctx = nil 
      let kctx = ["Maybe" |-> Star :->*: Star]
      let fctx = ["Just" |-> E.forAll ["a"] ("a" @->: "Maybe" @@: "a")]
      let ctx = rd fctx kctx lctx
      runCheck ctx ("Just" @@ E.int 10) ("Maybe" @@: "Int") `shouldYield` (lctx <+ E.mname 0 := "Int")

    it "works with type-constructors (2)" $ do
      let lctx = nil 
      let kctx = ["Maybe" |-> Star :->*: Star]
      let fctx = ["Just" |-> E.forAll ["a"] ("a" @->: "Maybe" @@: "a")]
      let ctx = rd fctx kctx lctx
      runCheck ctx ("Just" @@ E.int 10) ("Maybe" @@: "Int") `shouldYield` (lctx <+ E.mname 0 := "Int")

    it "fails Just 10 <= forall a. Maybe a" $ do
      let lctx = nil 
      let kctx = ["Maybe" |-> Star :->*: Star, "Nat" |-> Star]
      let fctx = ["Just" |-> E.forAll ["a"] ("a" @->: "Maybe" @@: "a")]
      let ctx = rd fctx kctx lctx
      shouldFail $ runCheck ctx ("Just" @@ E.int 10) (E.forAll ["a"] $ "Maybe" @@: "a")
    
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
      let mk = rd' ["Bool" |-> Star]
      do let ctx = nil <+ "x" .: (E.forAll ["a"] $ "a" @->: "a")
         runCheck (mk ctx) ("x" @@ E.true) "Bool" `shouldYield` (ctx <+ E.mname 0 := "Bool")
      do let ctx = nil <+ "x" .: ("Int" @->: "Bool" @->: "Int")
         runCheck (mk ctx) ("x" @@ E.int 10) ("Bool" @->: "Int") `shouldYield` ctx
      do let ctx = nil <+ "x" .: ("Int" @->: "Bool" @->: "Int")
         runCheck (mk ctx) ("x" @@ E.int 10 @@ E.true) ("Int") `shouldYield` ctx
      do let ctx = nil <+ "x" .: (("Int" @->: "Bool") @->: "Bool")
         runCheck (mk ctx) ("x" @@ ("y" @-> E.true)) ("Bool") `shouldYield` ctx
    
    it "rejects invalid foralls" $ do
      let mk = rd' ["Bool" |-> Star, "Nat" |-> Star]
      do let ctx = nil 
         shouldFail $ runCheck (mk ctx) ("x" @-> "x") (E.forAll ["a","a"] $ "a" @->: "a") 


  describe "kindOf" $ do
    let kinds = [ ("List"  |-> Star :->*: Star)
                , ("Tuple" |-> Star :->*: Star :->*: Star)
                , ("Nat"   |-> Star)
                , ("a"     |-> Star)
                , ("b"     |-> Star)
                ]
    let runKindOf ks ctx ty =
          let (r, _, _) = runTypingM0 (kindOf ty) (mempty {trKinds = ks, trCtx = ctx} :: TypingRead ()) 
          in  r

    it "looks up kinds" $ do
      runKindOf kinds mempty "Nat" `shouldBe` Right Star

    it "infers arrow types to be kind *" $ do
      runKindOf kinds mempty ("Nat" @->: "Nat") `shouldBe` Right Star
      runKindOf kinds mempty ("List" @@: "Nat" @->: "List" @@: "Nat") `shouldBe` Right Star

    it "fails when type not found in ctx" $ do
      runKindOf [] mempty "Nat" `shouldSatisfy` isLeft
    
    let a = mempty <+ uni "a"
    let ab = mempty <+ uni "a" <+ uni "b"
    it "fails with partially applied types in arrows" $ do
      runKindOf kinds a ("List" @->: "a") `shouldSatisfy` isLeft
      runKindOf kinds ab ("Tuple" @@: "a" @->: "b") `shouldSatisfy` isLeft

    it "infers lists" $ do
      runKindOf kinds a ("List" @@: "a") `shouldBe` Right Star

    it "infers tuples (curried)" $ do
      runKindOf kinds a ("Tuple" @@: "a") `shouldBe` Right (Star :->*: Star)

    it "infers tuples" $ do
      runKindOf kinds ab ("Tuple" @@: "a" @@: "b") `shouldBe` Right Star

    it "infers tuples of lists" $ do
      runKindOf kinds ab ("Tuple" @@: ("List" @@: "a") @@: "b") `shouldBe` Right Star

    it "infers foralls" $ do
      runKindOf kinds mempty (E.forAll ["a"] $ "List" @@: "a") `shouldBe` Right Star
      runKindOf kinds mempty (E.forAll ["a", "b"] $ "Tuple" @@: "a" @@: "b") `shouldBe` Right Star
      runKindOf kinds mempty ((E.forAll ["a"] $ "a") @->: E.forAll ["a"] "a") `shouldBe` Right Star
      runKindOf kinds mempty (E.forAll ["a"] $ "List" @@: "a" @->: "a") `shouldBe` Right Star
