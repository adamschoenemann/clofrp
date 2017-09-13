{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module CloTT.Check.PolySpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)

import qualified CloTT.AST.Parsed  as E
import           CloTT.Check.Poly
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import           CloTT.TestUtils
-- import           CloTT.QuasiQuoter

-- import Fixtures



polySpec :: Spec
polySpec = do
  let nil = emptyCtx @()

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
      let put = nil <+ uni "put"
      insertAt' (exists "a") put ctx `shouldBe` Nothing
    it "succeds in context with elem" $ do
      let ctx = nil <+ marker "m" <+ exists "a" <+ uni "a"
      let put = nil <+ uni "put"
      insertAt' (exists "a") put ctx `shouldBe` Just (nil <+ marker "m" <++ put <+ uni "a")

  describe "subtypeOf" $ do
    let shouldYield (res, st, tree) ctx = 
          case res of
            Right ctx' -> ctx' `shouldBe` ctx
            Left err   -> failure $ show err ++ "\nProgress:\n" ++ show tree
    let shouldFail (res, st, tree) = res `shouldSatisfy` isLeft

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




--   it "checks primitives" $ do
--     E.check0 (E.nat 10) "Nat"  `shouldBe` Right ()
--     E.check0 E.true     "Bool" `shouldBe` Right ()
--     E.check0 E.unit     "Unit" `shouldBe` Right ()
--     E.check0 E.unit     "Bool" `shouldSatisfy` isLeft

--   it "checks variables" $ do
--     E.check (E.tyctx [("x", "Nat")]) (E.var "x") "Nat" `shouldBe` Right ()
--     E.check (E.tyctx [("f" ,"Nat" @->: "Nat")]) (E.var "f") ("Nat" @->: "Nat") `shouldBe` Right ()
--     E.check (E.tyctx [("x", "Nat")]) (E.var "x") "Bool" `shouldSatisfy` isLeft
  
--   it "checks applications" $ do
--     E.check (E.tyctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.nat 10) "Nat" `shouldBe` Right ()
--     E.check (E.tyctx [("f" , ("Nat" @->: "Bool") @->: "Unit")]) (E.var "f" @@ ("x" @-> E.true)) "Unit" `shouldBe` Right ()
--     E.check0 (E.the ("Nat" @->: "Nat") ("x" @-> "x") @@ E.nat 10) "Nat" `shouldBe` Right ()
--     E.check (E.tyctx [("f" ,"Nat" @->: "Nat")]) (E.var "f" @@ E.true)   "Nat" `shouldSatisfy` isLeft
  
--   it "checks tuples" $ do
--     E.check0 [unsafeExpr|(10,20)|] ("Tuple" @@: "Nat" @@: "Nat") `shouldBe` Right ()
--     E.check @() (E.tyctx [("x", "Nat"), ("f", "Nat" @->: "Bool")]) ("x" @* "f" @@ "x") ("Tuple" @@: "Nat" @@: "Bool")
--         `shouldBe` Right ()
--     E.check @() (E.tyctx [("x", "Nat")]) ("x" @* ("y" @-> "x")) ("Tuple" @@: "Nat" @@: ("Bool" @->: "Nat"))
--         `shouldBe` Right ()
--     E.check @() (E.tyctx [("x", "Nat")]) ("x" @* ("y" @-> "x")) ("Tuple" @@: "Nat" @@: ("Bool" @->: "Bool"))
--         `shouldSatisfy` isLeft
  
--   it "checks lambdas" $ do
--     E.check0 [unsafeExpr|\x -> x|]  ("Nat" @->: "Nat") `shouldBe` Right ()
--     E.check0 [unsafeExpr|\x -> 10|] ("Nat" @->: "Nat") `shouldBe` Right ()
--     E.check0 [unsafeExpr|\x -> \y -> x|] ("Bool" @->: "Nat"  @->: "Bool") `shouldBe` Right ()
--     E.check0 [unsafeExpr|\x -> \y -> x|] ("Nat"  @->: "Bool" @->: "Nat")  `shouldBe` Right ()
--     E.check0 [unsafeExpr|\x -> \y -> x|] ("Bool" @->: "Nat"  @->: "Nat")  `shouldSatisfy` isLeft
  
--   it "fails programs with invalid types (1)" $ do
--     let prog = [unsafeProg|
--       data Foo a = MkFoo a.
--       foo : Foo -> Nat.
--       foo = \x -> x.
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "fails programs with invalid types (2)" $ do
--     let prog = [unsafeProg|
--       data List a = Nil | Cons a (List a a).
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "fails programs with invalid types (3)" $ do
--     let prog = [unsafeProg|
--       data List = Nil | Cons a (List a).
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "succeeds for mono-types" $ do
--     let prog = [unsafeProg|
--       data Int = .
--       data IntList = Nil | Cons Int IntList.
--     |]
--     E.checkProg prog `shouldBe` Right ()

--   it "succeeds for poly-types" $ do
--     let prog = [unsafeProg|
--       data List a = Nil | Cons a (List a).
--     |]
--     E.checkProg prog `shouldBe` Right ()

--   it "fails wrong signatures (wrong kind)" $ do
--     let prog = [unsafeProg|
--       data List a = Nil | Cons a (List a).
--       data Int = .
--       head : List -> List Int.
--       head = \x -> x.
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "fails signatures without explicit foralls" $ do
--     let prog = [unsafeProg|
--       data List a = Nil | Cons a (List a).
--       listId : List a -> List a.
--       listId = \x -> x.
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft
  
--   it "succeeds with mutual recursive data" $ do
--     let prog = [unsafeProg|
--       data Foo = Bar | Baz Baz.
--       data Baz = MkBaz Foo.
--     |]
--     E.checkProg prog `shouldBe` Right ()

--   it "succeeds with explicit foralls" $ do
--     let prog = [unsafeProg|
--       data List a = Nil | Cons a (List a).
--       listId : forall a. List a -> List a.
--       listId = \x -> x.
--     |]
--     E.checkProg prog `shouldBe` Right ()
  
--   it "succeeds with simple id function" $ do
--     let prog = [unsafeProg|
--       id : forall a. a -> a.
--       id = \x -> x.
--     |]
--     E.checkProg prog `shouldBe` Right ()
  
--   it "succeeds with mono-types (1)" $ do
--     let prog = [unsafeProg|
--       data N = Z | S N.

--       zero : N.
--       zero = Z.

--       one : N.
--       one = S Z.

--       succ : N -> N.
--       succ = \n -> S n.

--       plus2 : N -> N.
--       plus2 = \n -> succ (succ n).

--       -- should fail when we stop having implicit general recursion
--       bottom : N -> N.
--       bottom = \n -> bottom n.
--     |]
--     E.checkProg prog `shouldBe` Right ()
  
--   it "checks pattern matches successfully (prog02)" $ do
--     E.checkProg prog02 `shouldBe` Right ()
  
--   it "errors when patterns are missing bindings" $ do
--     let prog = [unsafeProg|
--       data N = Z | S N.
--       plus : N -> N -> N.
--       plus = \m -> \n -> 
--         case m of
--           | Z -> n
--           | S -> m.
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "errors when patterns have too many bindings" $ do
--     let prog = [unsafeProg|
--       data N = Z | S N.
--       plus : N -> N -> N.
--       plus = \m -> \n -> 
--         case m of
--           | Z    -> n
--           | S m' n' -> m'.
--     |]
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "errors when patterns have different types" $ do
--     let prog = [unsafeProg|
--       data N = Z | S N.
--       data Foo = MkFoo.
--       plus : N -> N -> N.
--       plus = \m -> \n -> 
--         case m of
--           | Z     -> n
--           | MkFoo -> m.
--     |]
--     -- let Left err = E.checkProg prog in print err
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "errors when cases have different types" $ do
--     let prog = [unsafeProg|
--       data N = Z | S N.
--       data Foo = MkFoo.
--       plus : N -> N -> N.
--       plus = \m -> \n -> 
--         case m of
--           | Z     -> n
--           | S m'  -> MkFoo.
--     |]
--     -- let Left err = E.checkProg prog in print err
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "errors when matching with wrong constructor" $ do
--     let prog = [unsafeProg|
--       data N = Z | S N.
--       data Foo = MkFoo N.
--       plus : N -> N -> N.
--       plus = \m -> \n -> 
--         case m of
--           | MkFoo m' -> m.
--     |]
--     -- let Left err = E.checkProg prog in print err
--     E.checkProg prog `shouldSatisfy` isLeft

--   it "works with nested pattern matches" $ do
--     let prog = [unsafeProg|
--       data N       = Z | S N.
--       data NList   = Nil | Cons N NList.
--       data Bool    = True | False.

--       isZeroes : NList -> Bool.
--       isZeroes = \xs -> 
--         case xs of
--           | Nil -> True
--           | Cons Z xs' -> isZeroes xs'
--           | Cons (S n) xs' -> False.
--     |]
--     E.checkProg prog `shouldBe` Right ()
  
--   it "works with some mono-morphic examples" $ do
--     let prog = [unsafeProg|
--       data N       = Z | S N.
--       data NList   = Nil | Cons N NList.
--       data NMaybe  = NNothing | NJust N.
--       data NLMaybe = NLNothing | NLJust NList.
--       data Bool    = True | False.

--       leq : N -> N -> Bool.
--       leq = \m -> \n -> 
--         case m of
--           | Z -> True
--           | S m' -> case n of
--             | Z -> False
--             | S n' -> leq m' n'.

--       head : NList -> NMaybe.
--       head = \xs -> 
--         case xs of
--           | Nil -> NNothing
--           | Cons n xs' -> NJust n.
      
--       tail : NList -> NLMaybe.
--       tail = \xs -> 
--         case xs of
--           | Nil -> NLNothing
--           | Cons n xs' -> NLJust xs'.
      
--       append : NList -> NList -> NList.
--       append = \xs -> \ys -> 
--         case xs of
--           | Nil -> ys
--           | Cons n xs' -> Cons n (append xs' ys).
      
--     |]
--     -- let Left err = E.checkProg prog in print err
--     E.checkProg prog `shouldBe` Right ()

--   -- FIXME: We still don't support polymorphism, so this will fail.
--   it "works with some polymorphic examples" $ do
--     pending
--     -- let prog = [unsafeProg|
--     --   data N      = Z | S N.
--     --   data List a = Nil | Cons a (List a).

--     --   append : List N -> List N -> List N.
--     --   append = \xs -> \ys -> 
--     --     case xs of
--     --       | Nil -> ys
--     --       | Cons n xs' -> Cons n (append xs' ys).
--     -- |]
--     -- -- let Left err = E.checkProg prog in print err
--     -- E.checkProg prog `shouldBe` Right ()

-- kindOfSpec :: Spec
-- kindOfSpec = do
--   let kinds = [ ("List", Star :->*: Star)
--               , ("Tuple", Star :->*: Star :->*: Star)
--               , ("Nat", Star)
--               , ("a", Star)
--               , ("b", Star)
--               ]
--   let [listK, tupK, natK, aK, bK] = kinds

--   it "looks up kinds" $ do
--     E.kindOf (E.ctxk [natK]) "Nat" `shouldBe` Right Star

--   it "infers arrow types to be kind *" $ do
--     E.kindOf (E.ctxk [natK]) ("Nat" @->: "Nat") `shouldBe` Right Star
--     E.kindOf (E.ctxk [natK, listK]) ("List" @@: "Nat" @->: "List" @@: "Nat") `shouldBe` Right Star

--   it "fails when type not found in ctx" $ do
--     E.kindOf (E.ctxk []) "Nat" `shouldSatisfy` isLeft
  
--   it "fails with partially applied types in arrows" $ do
--     E.kindOf (E.ctxk [listK, aK]) ("List" @->: "a") `shouldSatisfy` isLeft

--   it "infers lists" $ do
--     E.kindOf (E.ctxk [listK, aK]) ("List" @@: "a") `shouldBe` Right Star

--   it "infers tuples (curried)" $ do
--     E.kindOf (E.ctxk [tupK, aK]) ("Tuple" @@: "a") `shouldBe` Right (Star :->*: Star)

--   it "infers tuples" $ do
--     E.kindOf (E.ctxk [tupK, aK, bK]) ("Tuple" @@: "a" @@: "b") `shouldBe` Right Star

--   it "infers tuples of lists" $ do
--     E.kindOf (E.ctxk [tupK, listK, aK, bK]) ("Tuple" @@: ("List" @@: "a") @@: "b") `shouldBe` Right Star

--   it "infers foralls" $ do
--     E.kindOf (E.ctxk [listK]) (E.forAll ["a"] $ "List" @@: "a") `shouldBe` Right Star
--     E.kindOf (E.ctxk [tupK])  (E.forAll ["a", "b"] $ "Tuple" @@: "a" @@: "b") `shouldBe` Right Star
--     E.kindOf (E.ctxk [tupK])  (E.forAll ["a"] "a" @->: E.forAll ["a"] "a") `shouldBe` Right Star