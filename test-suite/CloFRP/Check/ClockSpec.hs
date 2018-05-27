{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloFRP.Check.ClockSpec where

import Test.Tasty.Hspec

import CloFRP.Check.TestUtils
import qualified Fixtures
import CloFRP.QuasiQuoter
import CloFRP.Check.Prog
import CloFRP.Check.TypingM
import CloFRP.AST.Kind
import CloFRP.Context
import CloFRP.TestUtils
import CloFRP.Pretty

import qualified CloFRP.AST as E
import qualified CloFRP.Annotated  as A

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
    
    it "accepts application of tick to polymorphic def" $ do
      let Right prog = pprog [text|
        data Unit = MkUnit.
        foo : forall a (k : Clock). |>k a.
        foo = undefined.

        bar : Unit.
        bar = foo [<>].
      |]
      -- shouldFail $ runCheckProg mempty prog 
      runCheckProg mempty prog `shouldYield` ()
    
    it "checks program with data-decl and clocks" $ do
      let Right prog = pprog [text|
        data NowOrNext (k : Clock) a = Now a | Next (|>k a).
        data Bool = True | False.

        isNow : forall (k : Clock) a. NowOrNext k a -> Bool.
        isNow = \x -> 
          case x of
          | Now y -> True
          | Next y -> False
          end.

        not : Bool -> Bool.
        not = \b -> 
          case b of 
          | True -> False
          | False -> True
          end.

        isNext : forall (k : Clock) a. NowOrNext k a -> Bool.
        isNext = \x -> not (isNow x).
        
        nextOrElse : forall (k : Clock) a. |>k a -> NowOrNext k a -> |>k a.
        nextOrElse = \d non ->
          case non of
          | Now y -> d
          | Next y -> y
          end.

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

        id : forall a. a -> a.
        id = \x -> x.

        tid' : forall (k : Clock) a. |>k a -> |>k a.
        tid' = \d -> 
          let r = \\(af : k) -> id (d [af])
          in r.
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

        data Wrap a = Wrap a.
        -- let bindings are ignored in terms of the kappa-stable context judgment
        good3 : forall (k : Clock) a. a -> a.
        good3 = \x -> 
          case Wrap (\\(af : k) -> x) of
          | Wrap x' -> x' [<>]
          end.
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
          | Cons x xs' -> x
          end.

        tl : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
        tl = \xs ->
          case unfold xs of
          | Cons x xs' -> xs'
          end.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "checks wrapped coinductive streams" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).
        data CoStream a = Cos (forall (k : Clock). Stream k a).

        uncos : forall a. CoStream a -> forall (k : Clock). Stream k a.
        uncos = \xs -> case xs of | Cos xs' -> xs' end.

        cosid : forall a. CoStream a -> CoStream a.
        cosid = \x ->
          let x' = uncos x : forall (k' : Clock). Stream k' a 
          in Cos x'.
        
        -- functor
        map : forall (k : Clock) a b. (a -> b) -> |>k a -> |>k b.
        map = \f la -> \\(af : k) -> f (la [af]).

      |]
      runCheckProg mempty prog `shouldYield` ()
    

    it "rejects incorrect definition of 'cos'" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
        type Stream (k : Clock) a = Fix (StreamF k a).
        data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

        uncos : forall (k : Clock) a. CoStream a -> Stream k a.
        uncos = \xs -> case xs of | Cos xs' -> xs' end.

        -- cos' : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
        -- cos' = \x xs ->
        --         Cos {a} (fold (Cons {k} {a} x (\\(af : k) -> uncos {k} {a} (xs [af])))).

        -- NOTE: This is not supposed to type-check since k is already chosen
        cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
        cos = \x xs -> 
          Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). 
      |]
      shouldFail $ runCheckProg mempty prog

    it "implements some good old stream functions" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
        type Stream (k : Clock) a = Fix (StreamF k a).
        data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

        cos : forall a. a -> CoStream a -> CoStream a.
        cos = \x xs -> 
          let inner = fold (Cons x (\\(af : k) -> uncos (xs))) : forall (k : Clock). Stream k a
          in  Cos inner. 

        uncos : forall (k : Clock) a. CoStream a -> Stream k a.
        uncos = \s -> let Cos s' = s in s' {k}.
        -- uncos = \xs -> case xs of | Cos xs' -> xs'.

        cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
        cons = \x xs -> fold (Cons x xs).

        hdk : forall (k : Clock) a. Stream k a -> a.
        hdk = \xs ->
          case unfold xs of
          | Cons x xs' -> x
          end.

        tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
        tlk = \xs ->
          case unfold xs of
          | Cons x xs' -> xs'
          end.

        hd : forall a. CoStream a -> a.
        hd = \xs -> let Cons x xs' = unfold (uncos {K0} xs) in x.
        -- hd = \xs -> hdk {K0} (uncos xs).
        
        tl : forall a. CoStream a -> CoStream a.
        tl = \xs -> Cos (let Cons x xs' = unfold (uncos xs) in xs' [<>]).
        -- tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

        eok : forall (k : Clock) a. CoStream a -> Stream k a.
        eok = fix (\g x -> cons (hd x) (\\(af : k) -> g [af] (tl (tl x)))).

        eo : forall a. CoStream a -> CoStream a.
        eo = \xs -> Cos (eok xs).

        -- demonstrate inference with stupid identity
        id : forall (k : Clock) a. Stream k a -> Stream k a.
        id = 
          let fn = \g xs -> 
                case unfold xs of
                | Cons x xs' -> 
                  let ys = \\(af : k) -> g [af] (xs' [af])
                  in cons x xs'
                end
          in fix fn.

        map : forall (k : Clock) a b. (a -> b) -> Stream k a -> Stream k b.
        map = \f -> fix (\g xs ->
          let Cons x xs' = unfold xs in
          let ys = \\(af : k) -> g [af] (xs' [af]) in
          cons (f x) ys
        ).
        

        -- applicative structure        
        pure : forall (k : Clock) a. a -> |>k a.
        pure = \x -> \\(af : k) -> x.

        app : forall (k : Clock) a b. |>k (a -> b) -> |>k a -> |>k b.
        app = \lf la -> \\(af : k) -> 
          let f = lf [af] in
          let a = la [af] in
          f a.

        -- functor
        dmap : forall (k : Clock) a b. (a -> b) -> |>k a -> |>k b.
        dmap = \f la -> app (pure f) la.

        data NatF f = Z | S f deriving Functor.
        type Nat = Fix NatF.

        z : Nat.
        z = fold Z.

        s : Nat -> Nat.
        s = \x -> fold (S x).

        nats : forall (k : Clock). Stream k Nat.
        nats = fix (\g -> cons z (dmap (map s) g)).
        -- nats = fix (\g -> cons z (\\(af : k) -> map (\x -> s x) (g [af]))).


        nth : Nat -> CoStream Nat -> Nat.
        nth = \n xs ->
          let Cos xs' = xs in
          let fn = \n xs' ->
            case n of
            | Z -> hdk xs'
            | S (n', r) -> r (tlk xs' [<>])
            end
          in  primRec {NatF} fn n xs'.
        
        test : forall (k' : Clock) a. |>k' (CoStream a) -> |>k' (Stream k' a).
        test = \xs -> \\(af : k') -> 
          let h = hdk (uncos (xs [af])) in
          let t = tlk (uncos (xs [af])) in
          cons h t.

        data ListF a f = Nil | LCons a f deriving Functor.
        type List a = Fix (ListF a).

        nil : forall a. List a.
        nil = fold Nil.

        lcons : forall a. a -> List a -> List a.
        lcons = \x xs -> fold (LCons x xs).

        force : forall a. (forall (k : Clock). |>k a) -> forall (k : Clock). a.
        force = \x -> x {k} [<>].

        uncons : forall a. CoStream a -> (a, CoStream a).
        uncons = \xs ->
          let h = hd xs in
          let t = tl xs
          in  (h, t).

        takeBody : forall a. NatF (Nat, CoStream a -> List a) -> CoStream a -> List a.
        takeBody = \m xs ->
          case m of
          | Z -> nil
          | S (m', r) -> 
            let (x, xs') = uncons xs
            in lcons x (r xs')
          end.

        take : forall a. Nat -> CoStream a -> List a.
        take = \n -> primRec {NatF} takeBody n.

        maapk : forall (k : Clock) a b. (a -> b) -> CoStream a -> Stream k b.
        maapk = \f ->
          fix (\g xs -> 
            let fhd = f (hd xs) in
            let ftltl = \\(af : k) -> g [af] (tl (tl xs)) in
            let ftl = \\(af : k) -> cons (f (hd (tl xs))) ftltl in
            cons fhd ftl
          ).
        
        maap : forall a b. (a -> b) -> CoStream a -> CoStream b.
        maap = \f xs -> Cos (maapk f xs).

        data Bool = True | False.        
        truefalse : forall (k : Clock). Stream k Bool.
        truefalse = fix (\g -> cons True (\\(af : k) -> cons False g)).

        trues : Stream K0 Bool.
        trues = 
          let Cos xs = eo (Cos truefalse) in
          xs.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "checks simple corecursive trees with tuple" $ do
      let Right prog = pprog [text|
        data TreeF (k : Clock) a f = Branch a (|>k f, |>k f).
        type Tree (k : Clock) a = Fix (TreeF k a).
        data Unit = MkUnit.

        constTree : forall (k : Clock) a. a -> Tree k a.
        constTree = \x ->
          fix (\g -> fold (Branch x (g, g))).

        main : Tree K0 Unit.
        main = constTree MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "implements replaceMin" $ do
      let Right prog = pprog Fixtures.replaceMin
      runCheckProg mempty prog `shouldYield` ()

    it "implements stream processing" $ do
      let Right prog = pprog Fixtures.streamProcessing
      runCheckProg mempty prog `shouldYield` ()

      
