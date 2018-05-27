{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ReplaceMin (main) where

import Prelude hiding (fst, snd, map, pure, min)
import Data.Functor.Classes

import CloFRP.Compiler
import CloFRP.QuasiQuoter

[hsclofrp|
  -- applicative structure        
  pure : forall (k : Clock) a. a -> |>k a.
  pure = \x -> \\(af : k) -> x.

  app : forall (k : Clock) a b. |>k (a -> b) -> |>k a -> |>k b.
  app = \lf la -> \\(af : k) -> 
    let f = lf [af] in
    let a = la [af] in
    f a.

  -- functor
  map : forall (k : Clock) a b. (a -> b) -> |>k a -> |>k b.
  map = \f la -> app (pure f) la.

  fst : forall a b. (a, b) -> a.
  fst = \x -> case x of | (y, z) -> y end.

  snd : forall a b. (a, b) -> b.
  snd = \x -> case x of | (y, z) -> z end.

  feedback : forall (k : Clock) (b : Clock -> *) u. (|>k u -> (b k, u)) -> b k.
  feedback = \f -> fst (fix (\x -> f (map snd x))).

  data NatF f = Z | S f deriving Functor.
  type Nat = Fix NatF.
  extern data Bool = True | False.

  z : Nat.
  z = fold Z.

  s : Nat -> Nat.
  s = \x -> fold (S x).

  plus : Nat -> Nat -> Nat.
  plus = \m n -> 
    let body = \x ->
      case x of
      | Z -> n
      | S (m', r) -> fold (S r)
      end
    in  primRec {NatF} body m.

  mult : Nat -> Nat -> Nat.
  mult = \m n ->
    let body = \x -> 
      case x of
      | Z -> z
      | S (m', r) -> plus n r
      end
    in primRec {NatF} body m.

  data TreeF a f = Leaf a | Br f f deriving Functor.
  type Tree a = Fix (TreeF a).

  ite : forall a. Bool -> a -> a -> a.
  ite = \b x y ->
    case b of
    | True -> x
    | False -> y
    end.

  min : Int -> Int -> Int.
  min = \x y -> ite (x < y) x y.

  leaf : forall a. a -> Tree a.
  leaf = \x -> fold (Leaf x).

  br : forall a. Tree a -> Tree a -> Tree a.
  br = \l r -> fold (Br l r).

  data Delay a (k : Clock) = Delay (|>k a).

  replaceMinBody : forall (k : Clock). Tree Int -> |>k Int -> (Delay (Tree Int) k, Int).
  replaceMinBody = primRec {TreeF Int} (\t m ->
    case t of
    | Leaf x -> (Delay (map leaf m), x)
    | Br (l, lrec) (r, rrec) -> 
      let (Delay l', ml) = lrec m {- : (Delay (Tree Int) k, Int) -} in
      let (Delay r', mr) = rrec m {- : (Delay (Tree Int) k, Int) -} in
      let m'       = min ml mr in
      (Delay (app (map br l') r'), m')
    end
  ).

  replaceMin : Tree Int -> Tree Int.
  replaceMin = \t -> 
    let Delay t' = feedback {K0} (replaceMinBody t) 
    in t' [<>].
  
  ofHeight : Nat -> Tree Int.
  ofHeight = \nat -> 
    fst (primRec {NatF} (\m n ->
      case m of  
      | Z -> (leaf n, 1 + n)
      | S (m', r) -> 
        let (t1, n1) = r n in
        let (t2, n2) = r n1
        in  (br t1 t2, n2)
      end
    ) nat 0).
  
  main : Tree Int.
  main = 
    let five = s (s (s (s (s z)))) in
    let four = s (s (s (s z)))
    in  replaceMin (ofHeight (mult four five)).
|]

-- instance Show a => Show1 (TreeF a) where 
--   liftShowsPrec sp sl _ t = 
--     case t of
--       Leaf x = ("Leaf" ++) . (shows x)
--       Br l r = 

instance Show a => Show1 (TreeF a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance Show2 TreeF where
  liftShowsPrec2 sa  _ _  _ _ (Leaf x) = showString "Nil" . sa 0 x
  liftShowsPrec2 sa _ sb _ d (Br l r)  = showParen (d > 10)
    $ showString "Br "
    . sb 11 l
    . showString " "
    . sb 11 r

