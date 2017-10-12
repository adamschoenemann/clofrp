{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.Poly.RecSpec where

import Test.Tasty.Hspec

import           CloTT.Check.Poly.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Check.Poly.Prog
import           CloTT.Check.Poly.TypingM
import           CloTT.Pretty
import           CloTT.AST.Name

recSpec :: Spec 
recSpec = do
  let errs e x = fst x `shouldBe` e
  describe "recursive types" $ do
    it "works in very simple cases (Nat)" $ do
      let prog = [unsafeProg|
        data NatF a = Z | S a.
        type Nat = Fix x. NatF x.

        foldNat' : NatF (Fix x. NatF x) -> Fix x. NatF x.
        foldNat' = \m -> fold m.

        foldNat : NatF Nat -> Nat.
        foldNat = \m -> fold m.

        unfoldNat' : (Fix x. NatF x) -> NatF (Fix x. NatF x).
        unfoldNat' = \m -> unfold m.

        unfoldNat : Nat -> NatF Nat.
        unfoldNat = \m -> unfold m.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works in slightly more complex case (Nat)" $ do
      let prog = [unsafeProg|
        data NatF a = Z | S a.
        type Nat = Fix x. NatF x.

        unfoldFold : Nat -> Nat.
        unfoldFold = \m -> fold (unfold m).

        foldUnfold : NatF Nat -> NatF Nat.
        foldUnfold = \m -> unfold (fold m).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works with some pattern matching (Nat)" $ do
      let prog = [unsafeProg|
        data NatF a = Z | S a.
        type Nat = Fix x. NatF x.

        -- pred : Nat -> Nat.
        -- pred = \m ->
        --   case unfold m of
        --     | Z -> fold Z
        --     | S m' -> m'.

        -- pred2 : Nat -> Nat.
        -- pred2 = \m ->
        --   case unfold m of
        --     | S m' -> case unfold m' of
        --       | Z -> fold Z
        --       | S m'' -> m''
        --     | Z -> fold Z.
        
        -- succ : Nat -> Nat.
        -- succ = \x -> fold (S x).

        plus2 : Nat -> Nat.
        plus2 = \x -> fold (S (fold (S x))).

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works in very simple cases (List)" $ do
      let prog = [unsafeProg|
        data ListF a f = Nil | Cons a f.
        type List a = Fix x. ListF a x.

        foldList' : forall a. ListF a (Fix x. ListF a x) -> Fix x. ListF a x.
        foldList' = \m -> fold m.

        foldList : forall a. ListF a (List a) -> List a.
        foldList = \m -> fold m.

        unfoldList' : forall a. (Fix x. ListF a x) -> ListF a (Fix x. ListF a x).
        unfoldList' = \m -> unfold m.

        unfoldList : forall a. List a -> ListF a (List a).
        unfoldList = \m -> unfold m.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works with some pattern matching (List)" $ do
      let prog = [unsafeProg|
        data ListF a f = Nil | Cons a f.
        type List a = Fix x. ListF a x.

        data Maybe a = Nothing | Just a.

        head : forall a. List a -> Maybe a.
        head = \xs ->
          case unfold xs of
            | Nil -> Nothing
            | Cons x xs' -> Just x.
        
        singleton : forall a. a -> List a.
        singleton = \x -> fold (Cons x (fold Nil)).
        -- singleton = \x -> fold (Cons x (the (Fix f. ListF a f) (fold Nil))).
      |]
      runCheckProg mempty prog `shouldYield` ()