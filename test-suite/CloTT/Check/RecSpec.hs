{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.RecSpec where

import Test.Tasty.Hspec

import           CloTT.Check.TestUtils
import           CloTT.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Check.Prog
import           CloTT.Check.TypingM
import           CloTT.Pretty
import           CloTT.AST.Name

recSpec :: Spec 
recSpec = do
  -- let errs e x = fst x `shouldBe` e
  describe "recursive types" $ do
    it "works in very simple cases (Nat)" $ do
      let Right prog = pprog [text|
        data NatF a = Z | S a deriving Functor.
        type Nat = Fix NatF.

        foldNat' : NatF (Fix NatF) -> Fix NatF.
        foldNat' = \m -> fold m.

        foldNat : NatF Nat -> Nat.
        foldNat = \m -> fold m.

        foldNatPF : NatF Nat -> Nat.
        foldNatPF = fold.

        unfoldNat' : Fix NatF -> NatF (Fix NatF).
        unfoldNat' = \m -> unfold m.

        unfoldNat : Nat -> NatF Nat.
        unfoldNat = \m -> unfold m.

        unfoldNatPF : Nat -> NatF Nat.
        unfoldNatPF = unfold.

        zero : Nat.
        zero = fold Z.

        one : Nat.
        one = fold (S (fold Z)).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works in slightly more complex case (Nat)" $ do
      let Right prog = pprog [text|
        data NatF a = Z | S a.
        type Nat = Fix NatF.

        unfoldFold : Nat -> Nat.
        unfoldFold = \m -> fold (unfold m).

        foldUnfold : NatF Nat -> NatF Nat.
        foldUnfold = \m -> unfold (fold m).

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works with some pattern matching (Nat)" $ do
      let Right prog = pprog [text|
        data NatF a = Z | S a.
        type Nat = Fix NatF.

        pred : Nat -> Nat.
        pred = \m ->
          case unfold m of
            | Z -> fold Z
            | S m' -> m'.

        pred2 : Nat -> Nat.
        pred2 = \m ->
          case unfold m of
            | S m' -> case unfold m' of
              | Z -> fold Z
              | S m'' -> m''
            | Z -> fold Z.
        
        succ : Nat -> Nat.
        succ = \x -> fold (S x).

        plus2 : Nat -> Nat.
        plus2 = \x -> fold (S (fold (S x))).

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works in very simple cases (List)" $ do
      let Right prog = pprog [text|
        data ListF a f = Nil | Cons a f.
        type List a = Fix (ListF a).

        foldList' : forall a. ListF a (Fix (ListF a)) -> Fix (ListF a).
        foldList' = \m -> fold m.

        foldList : forall a. ListF a (List a) -> List a.
        foldList = \m -> fold m.

        unfoldList' : forall a. (Fix (ListF a)) -> ListF a (Fix (ListF a)).
        unfoldList' = \m -> unfold m.

        unfoldList : forall a. List a -> ListF a (List a).
        unfoldList = \m -> unfold m.

        nil : forall a. List a.
        nil = fold Nil.

        cons : forall a. a -> List a -> List a.
        cons = \x xs -> fold (Cons x xs).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works with some pattern matching (List)" $ do
      let Right prog = pprog [text|
        data ListF a f = Nil | Cons a f.
        type List a = Fix (ListF a).

        data Maybe a = Nothing | Just a.

        foldList : forall a. ListF a (List a) -> List a.
        foldList = \x -> fold x.
        
        head : forall a. List a -> Maybe a.
        head = \xs ->
          case unfold xs of
            | Nil -> Nothing
            | Cons x xs' -> Just x.
        
        singleton : forall a. a -> List a.
        singleton = \x -> fold (Cons x (fold Nil)).

        singleton' : forall a. a -> List a.
        singleton' = \x -> foldList (Cons x (foldList Nil)).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works with Trees" $ do
      let Right prog = pprog [text|
        data TreeF a f = Empty | Branch a f f.
        type Tree a = Fix (TreeF a).

        data NatF a = Z | S a.
        type Nat = Fix NatF.

        data Maybe a = Nothing | Just a.
        data Triple a b c = Triple a b c.

        empty : forall a. Tree a.
        empty = fold Empty.

        branch : forall a. a -> Tree a -> Tree a -> Tree a.
        branch = \x l r -> fold (Branch x l r).

        treeMatch : forall a. Tree a -> Maybe (Triple a (Tree a) (Tree a)).
        treeMatch = \t ->
          case unfold t of
            | Empty -> Nothing
            | Branch x l r -> Just (Triple x l r).

        nonsense : forall a. Tree a -> Nat.
        nonsense = \t -> 
          case unfold t of
            | Empty -> fold Z
            | Branch x l r -> fold (S (fold Z)).

      |]
      runCheckProg mempty prog `shouldYield` ()
    
    specify "primRec with Nat" $ do
      let Right prog = pprog [text|
        data NatF a = Z | S a deriving Functor. 
        type Nat = Fix NatF.

        plusRec : Nat -> NatF (Nat, Nat) -> Nat.
        plusRec = \n x ->
          case x of
            | Z -> n
            | S (m', r) -> fold (S r).
        
        -- without annotations :O
        plus : Nat -> Nat -> Nat.
        plus = \m n -> 
          let body = \x ->
            case x of
              | Z -> n
              | S (m', r) -> fold (S r)
          in  primRec {NatF} body m.

        multRec : Nat -> NatF (Nat, Nat) -> Nat.
        multRec = \n x ->
          case x of
            | Z -> fold Z
            | S (m', r) -> plus n r.
        
        mult : Nat -> Nat -> Nat.
        mult = \m n ->
          primRec {NatF} (multRec n) m.

        -- without annotations :O
        mult' : Nat -> Nat -> Nat.
        mult' = \m n ->
          let body = \x -> case x of
            | Z -> fold Z
            | S (m', r) -> plus n r
          in primRec {NatF} body m.

      |]
      runCheckProg mempty prog `shouldYield` ()

    specify "primRec with List" $ do
      let Right prog = pprog [text|
        data ListF a f = Nil | Cons a f deriving Functor.
        type List a = Fix (ListF a).

        mapRec : forall a b. (a -> b) -> ListF a (List a, List b) -> List b.
        mapRec = \f l->
          case l of
            | Nil -> fold Nil
            | Cons x (xs, ys) -> fold (Cons (f x) ys).

        map : forall a b. (a -> b) -> List a -> List b.
        map = \f xs -> primRec {ListF a} (mapRec f) xs.

        -- without annotations :O
        map' : forall a b. (a -> b) -> List a -> List b.
        map' = \f xs -> 
          let body = \x -> 
            case x of
              | Nil -> fold Nil
              | Cons x (xs, ys) -> fold (Cons (f x) ys)
          in  primRec {ListF a} body xs.

        type Fmap (f : * -> *) = forall a b. (a -> b) -> f a -> f b.
        data Functor (f : * -> *) = Functor (Fmap f).

        -- we have to wrap it in a "newtype" to make it a functor
        data ListW a = ListW (Fix (ListF a)).

        listf : forall a. Functor ListW.
        listf = Functor (\f l -> 
          case l of  
            | ListW ls -> ListW (map f ls)
        ).

      |]
      runCheckProg mempty prog `shouldYield` ()

    specify "primRec with Tree" $ do
      let Right prog = pprog [text|
        data TreeF a f = Empty | Branch a f f deriving Functor.
        type Tree a = Fix (TreeF a).

        mapRec : forall a b. (a -> b) -> TreeF a (Tree a, Tree b) -> Tree b.
        mapRec = \f t ->
          case t of
            | Empty -> fold Empty
            | Branch x (l, lrec) (r, rrec) -> fold (Branch (f x) lrec rrec).

        map : forall a b. (a -> b) -> Tree a -> Tree b.
        map = \f xs -> primRec {TreeF a} (mapRec f) xs.

        -- -- without annotations :O
        map' : forall a b. (a -> b) -> Tree a -> Tree b.
        map' = \f xs -> 
          let body = \t -> 
            case t of
              | Empty -> fold Empty
              | Branch x (l, lrec) (r, rrec) -> fold (Branch (f x) lrec rrec)
          in  primRec {TreeF a} body xs.

      |]
      runCheckProg mempty prog `shouldYield` ()
