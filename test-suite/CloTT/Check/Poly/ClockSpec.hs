{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.Poly.ClockSpec where

import Test.Tasty.Hspec

import CloTT.Check.Poly.TestUtils
import CloTT.QuasiQuoter
import CloTT.Check.Poly.Prog
import CloTT.Check.Poly.TypingM
import CloTT.AST.Kind
import CloTT.Context
import CloTT.TestUtils
import CloTT.Pretty

import qualified CloTT.AST.Parsed as E
import qualified CloTT.Annotated  as A

clockSpec :: Spec 
clockSpec = do
  let errs e x = (A.unann . fst $ x) `shouldBe` e
  let mname = A.A () . E.TVar . E.mname
  describe "clocks" $ do
    it "accepts veeery simple programs with clock quantification" $ do
      let prog = [unsafeProg|
        foo : forall (k : Clock) a. a -> a.
        foo = \x -> x. 
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "accepts veeery simple programs with clock application (1)" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        idk : forall (k : Clock) a. a -> a.
        idk = \x -> x. 

        bar : forall (k : Clock). Unit.
        bar = idk {k} MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "accepts veeery simple programs with clock application (2)" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        idk : forall (k : Clock) (k' : Clock) a. a -> a.
        idk = \x -> x. 

        bar : forall (k : Clock). Unit.
        bar = idk {k} {k} MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "rejects veeery simple programs with clock application (1)" $ do
      let Right prog = pprog [text|
        idk : forall (k : Clock) a. |>k a -> |>k a.
        idk = \x -> x. 

        bar : forall (k : Clock) (k' : Clock) a. |>k a -> |>k' a.
        bar = \x -> idk {k'} x.
      |]
      runCheckProg mempty prog `shouldFailWith` (errs $ (mname 0) `CannotSubtype` (mname 1))
    
    it "checks program with data-decl and clocks" $ do
      let Right prog = pprog [text|
        data NowOrNext (k : Clock) a = Now a | Next (|>k a).
        data Bool = True | False.

        isNow : forall (k : Clock) a. NowOrNext k a -> Bool.
        isNow = \x -> case x of
          | Now y -> True
          | Next y -> False.

        not : Bool -> Bool.
        not = \b -> case b of 
          | True -> False
          | False -> True.

        isNext : forall (k : Clock) a. NowOrNext k a -> Bool.
        isNext = \x -> not (isNow x).
        
        nextOrElse : forall (k : Clock) a. |>k a -> NowOrNext k a -> |>k a.
        nextOrElse = \d non ->
          case non of
            | Now y -> d
            | Next y -> y.

      |]
      let (Right ep, _st, _wrt) = runTypingM0 (elabProg prog) mempty 
      case query "NowOrNext" (kinds ep ) of
        Just k -> k `shouldBe` ClockK :->*: Star :->*: Star
        Nothing -> failure "NowOrNext"
      runCheckProg mempty prog `shouldYield` ()
    
    it "accepts simple prog with tick abstraction and application" $ do
      let Right prog = pprog [text|
        tid : forall (k : Clock) a. |>k a -> |>k a.
        tid = \d -> \\(af : k) -> d [af].
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "rejects non-productive program with tick constant application" $ do
      let Right prog = pprog [text|
        bad : forall (k : Clock) a. |>k a -> a.
        bad = \d -> d [<>].
      |]
      runCheckProg mempty prog `shouldFailWith` (errs $ Other "Context not stable wrt `a due to d λ: ⊳`a `b")

    it "accepts productive program with tick constant application (1)" $ do
      let Right prog = pprog [text|
        good : forall (k : Clock) a. a -> a.
        good = \x -> (\\(af : k) -> x) [<>].

        -- let bindings are ignored in terms of the kappa-stable context judgment
        good2 : forall (k : Clock) a. a -> a.
        good2 = \x -> 
          let x' = (\\(af : k) -> x)
          in  x' [<>].
      |]
      runCheckProg mempty prog `shouldYield` ()
      
    it "rejects beta-equivalent def of id (productive but we cannot type it)" $ do
      let Right prog = pprog [text|
        data Wrap a = MkWrap a.

        foo : forall (k : Clock) a. |>k a -> |>k a.
        foo = \x -> (\\(af : k) -> x) [<>].
      |]
      runCheckProg mempty prog `shouldFailWith` (errs $ Other "Context not stable wrt `a due to x λ: ⊳`a `b")

    it "accepts the encoding of the force" $ do
      let Right prog = pprog [text|
        force : forall a. (forall (k : Clock). |>k a) -> forall (k : Clock). a.
        force = \x -> x {k} [<>].
      |]
      runCheckProg mempty prog `shouldYield` ()
  
  describe "fix" $ do
    it "has the correct type" $ do
      let Right prog = pprog [text|
        fix' : forall (k : Clock) a. (|>k a -> a) -> a.
        fix' = fix.

        fix'' : forall (k : Clock) a. (|>k a -> a) -> a.
        fix'' = \x -> fix x.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "implements the constant guarded stream" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).
        
        repeat : forall (k : Clock) a. a -> Stream k a.
        repeat = \x ->
          let body = (\xs -> fold (Cons x xs)) 
          in  fix body.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "implements the example from the 'clocks are ticking' paper" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).
        
        cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
        cons = \x xs -> fold (Cons x xs).

        hd : forall (k : Clock) a. Stream k a -> a.
        hd = \xs ->
          case unfold xs of
          | Cons x xs' -> x.

        tl : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
        tl = \xs ->
          case unfold xs of
          | Cons x xs' -> xs'.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "implements some good old stream functions" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).

        -- demonstrate inference with stupid identity
        id : forall (k : Clock) a. Stream k a -> Stream k a.
        id = fix (\g xs -> 
          case unfold xs of
          | Cons x xs' -> 
            let ys = \\(af : k) -> g [af] (xs' [af])
            in  fold (Cons x ys)
        ).

        -- mapfix : forall (k : Clock) a b. (a -> b) -> |>k (Stream k a -> Stream k b) -> Stream k a -> Stream k b.
        -- mapfix = \f g xs ->
        --   case unfold xs of
        --   | Cons x xs' -> 
        --     let ys = \\(af : k) -> g [af] (xs' [af])
        --     in  fold (Cons (f x) ys).

        map : forall (k : Clock) a b. (a -> b) -> Stream k a -> Stream k b.
        map = \f -> 
          let mapfix = \f g xs ->
                case unfold xs of
                | Cons x xs' -> 
                  let ys = \\(af : k) -> g [af] (xs' [af])
                  in  fold (Cons (f x) ys)
          in fix (mapfix f).
      |]
      runCheckProg mempty prog `shouldYield` ()

      