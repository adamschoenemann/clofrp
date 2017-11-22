{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeApplications #-}

module Fixtures where

import CloTT.QuasiQuoter
import NeatInterpolation

import qualified CloTT.Parser.Expr as P
-- import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Decl as P
import qualified CloTT.Parser.Prog as P
import Data.Text (Text)

expr01 :: P.Expr
expr01 = [unsafeExpr|\x -> \y -> the (Nat) (x y True)|]

decl01 :: P.Decl
decl01 = [unsafeDecl|data Tree a = Leaf | Branch a (Tree a) (Tree a).|]

prog01, prog02 :: P.Prog
prog01 = [unsafeProg|
  id : a -> a.
  id = \x -> x.

  twice : Nat -> Tuple Nat Nat.
  twice = \x -> (x, x).

  data Maybe a = Nothing | Just a.
  data List a = Nil | Cons a (List a).

  head : List a -> Maybe a.
  head = \xs -> xs.
|]

prog02 = [unsafeProg|
  data N = Z | S N.
  plus : N -> N -> N.
  plus = \m -> \n -> 
    case m of
      | Z    -> n
      | S m' -> S (plus m' n).
|]

replaceMin :: Text
replaceMin = 
  [text|
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
      fst = \x -> case x of | (y, z) -> y.

      snd : forall a b. (a, b) -> b.
      snd = \x -> case x of | (y, z) -> z.

      feedback : forall (k : Clock) (b : Clock -> *) u. (|>k u -> (b k, u)) -> b k.
      feedback = \f -> fst (fix (\x -> f (map snd x))).

      data NatF f = Z | S f deriving Functor.
      type Nat = Fix NatF.

      z : Nat.
      z = fold Z.

      s : Nat -> Nat.
      s = \x -> fold (S x).

      data TreeF a f = Leaf a | Br f f deriving Functor.
      type Tree a = Fix (TreeF a).

      min : Nat -> Nat -> Nat.
      min = primRec {NatF} (\m n -> 
        case m of 
        | Z -> fold Z
        | S (m', r) -> fold (S (r n))
      ).

      leaf : forall a. a -> Tree a.
      leaf = \x -> fold (Leaf x).

      br : forall a. Tree a -> Tree a -> Tree a.
      br = \l r -> fold (Br l r).

      data Delay a (k : Clock) = Delay (|>k a).

      replaceMinBody : forall (k : Clock). Tree Nat -> |>k Nat -> (Delay (Tree Nat) k, Nat).
      replaceMinBody = primRec {TreeF Nat} (\t m ->
        case t of
        | Leaf x -> (Delay (map leaf m), x)
        | Br (l, lrec) (r, rrec) -> 
          let (Delay l', ml) = lrec m {- : (Delay (Tree Nat) k, Nat) -} in
          let (Delay r', mr) = rrec m {- : (Delay (Tree Nat) k, Nat) -} in
          let m'       = min ml mr in
          (Delay (app (map br l') r'), m')
      ).

      replaceMinK : forall (k : Clock). Tree Nat -> Delay (Tree Nat) k.
      replaceMinK = \t -> feedback (replaceMinBody t).

      replaceMin : Tree Nat -> Tree Nat.
      replaceMin = \t -> 
        let Delay t' = replaceMinK {K0} t
        in t' [<>].
      
      ofHeight : Nat -> Tree Nat.
      ofHeight = \nat -> 
        fst (primRec {NatF} (\m n ->
          case m of  
            | Z -> (leaf z, s n)
            | S (m', r) -> 
              let (t1, n1) = r n in
              let (t2, n2) = r n1
              in  (br t1 t2, n2)
        ) nat z).
      
      main : Tree Nat.
      main = 
        let five = s (s (s (s (s z))))
        in  replaceMin (ofHeight five).
    |]

streamProcessing :: Text
streamProcessing = 
  [text|
    data SPF i o (k : Clock) f
      = Get (i -> f)
      | Put o (|>k f)
      deriving Functor.
    
    type SP i o (k : Clock) = Fix (SPF i o k).

    step : forall (k : Clock) i o. SP i o k -> SPF i o k (Fix (SPF i o k)).
    step = unfold.

    data StreamF (k : Clock) a f = Cons a (|>k f).
    type Stream (k : Clock) a = Fix (StreamF k a).
    data CoStream a = Cos (forall (k : Clock). Stream k a).

    hd : forall a. CoStream a -> a.
    hd = \xs -> 
      let Cos s = xs
      in case unfold s of
          | Cons x xs' -> x.

    -- see if you can do this better with let generalization
    tl : forall a. CoStream a -> CoStream a.
    tl = \x ->
      let Cos s = x in
      let r = (case unfold s of
              | Cons x xs' -> xs' 
              ) : forall (k : Clock). |>k (Stream k a)
      in Cos (r [<>]).

    fst : forall a b. (a, b) -> a.
    fst = \x -> case x of | (y, z) -> y.

    snd : forall a b. (a, b) -> b.
    snd = \x -> case x of | (y, z) -> z.

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

    -- fixpoint above with full types
    applyfix : forall (k : Clock) i o. |>k (SP i o k -> CoStream i -> CoStream o) -> SP i o k -> CoStream i -> CoStream o.
    applyfix = \rec -> 
      primRec {SPF i o k} (\x s ->
        case x of
        | Get f -> let (sp', g) = f (hd s) in g (tl s)
        | Put b sp -> 
          let sp1 = map fst sp in
          cos b (app (app rec sp1) (pure s))
      ).

    -- it even works without annotations!
    apply : forall (k : Clock) i o. SP i o k -> CoStream i -> CoStream o.
    apply = fix (\rec -> 
      primRec {SPF i o k} (\x s ->
        case x of
        | Get f -> (snd (f (hd s))) (tl s) 
        | Put b sp -> 
          let sp1 = map fst sp in
          cos b (app (app rec sp1) (pure s))
      )).

    cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
    cos = \x xs -> 
      Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). 

    uncos : forall (k : Clock) a. CoStream a -> Stream k a.
    uncos = \xs -> case xs of | Cos xs' -> xs'.

    spid : forall i. SP i i K0.
    spid = fix (\f -> fold (Get (\i -> fold (Put i f)))).

    const : forall (k : Clock) a. a -> Stream k a.
    const = \x -> fix (\f -> fold (Cons x f)).

    data Unit = MkUnit.

    main : Stream K0 Unit.
    main = uncos (apply spid (Cos (const MkUnit))).
  |]
