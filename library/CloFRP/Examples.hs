{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloFRP.Examples where

import CloFRP.Interop
import CloFRP.QuasiQuoter
import Text.Parsec.Pos

type CTStream = 'CTFree "Stream" :@: 'CTFree "K0"
type CTNat = 'CTFree "Nat"
type CTInt = 'CTFree "Int"

clofrp_const :: CloFRP ('CTFree "Stream" ':@: 'CTFree "K0" ':@: 'CTFree "Unit") SourcePos
clofrp_const = [clofrp|
  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).
  data Unit = MkUnit.
  const : forall (k : Clock) a. a -> Stream k a.
  const = \x -> fix (\g -> fold (Cons x g)).
  main : Stream K0 Unit.
  main = const MkUnit.
|]


clott_add :: CloFRP (CTStream :@: CTTuple [CTNat, CTNat] :->: CTStream :@: CTNat) SourcePos
clott_add = [clofrp|
  data NatF f = Z | S f deriving Functor.
  type Nat = Fix (NatF).
  s : Nat -> Nat.
  s = \x -> fold (S x).
  z : Nat.
  z = fold Z.

  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).

  plus : Nat -> Nat -> Nat.
  plus = \m n -> 
    let body = \x ->
      case x of
        | Z -> n
        | S (m', r) -> s r
    in  primRec {NatF} body m.

  app : forall (k : Clock) a b. |>k (a -> b) -> |>k a -> |>k b.
  app = \lf la -> \\(af : k) -> 
    let f = lf [af] in
    let a = la [af] in
    f a.

  main : Stream K0 (Nat, Nat) -> Stream K0 Nat.
  main = 
    fix (\g pairs -> 
      case unfold pairs of   
        | Cons pair xs -> 
          case pair of
          | (x1, x2) -> fold (Cons (plus x1 x2) (app g xs))
    ).
|]

clott_add_int :: CloFRP (CTStream :@: CTTuple [CTInt, CTInt] :->: CTStream :@: CTInt) SourcePos
clott_add_int = [clofrp|
  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).

  app : forall (k : Clock) a b. |>k (a -> b) -> |>k a -> |>k b.
  app = \lf la -> \\(af : k) -> 
    let f = lf [af] in
    let a = la [af] in
    f a.

  main : Stream K0 (Int, Int) -> Stream K0 Int.
  main = 
    fix (\g pairs -> 
      let Cons (x1, x2) xs = unfold pairs
      in  fold (Cons (x1 + x2) (app g xs))
    ).
|]

[hsclofrp|
  extern data Bool = True | False.

  cfp_id : forall a. a -> a.
  cfp_id = \x -> x.

  false : Bool.
  false = False.

  negate : Bool -> Bool.
  negate = \b ->
    case b of
    | True -> False
    | False -> True.
  
  data NatF f = Z | S f deriving Functor.
  type Nat = Fix NatF.

  toInt : Nat -> Int.
  toInt = 
    let fn = \x -> case x of 
                   | Z -> 0
                   | S (n, r) -> 1 + r
    in  primRec {NatF} fn.
  z : Nat. z = fold Z.
  s : Nat -> Nat. s = \x -> fold (S x).
  five : Nat. 
  five = s (s (s (s (s z)))).

  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).
  data ListF a f = Nil | LCons a f.
  type List a = Fix (ListF a).

  cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
  cons = \x xs -> fold (Cons x xs).
  strconst : forall (k : Clock) a. a -> Stream k a.
  strconst = \x -> fix (\xs -> cons x xs).

  strmap : forall (k : Clock) a b. (a -> b) -> Stream k a -> Stream k b.
  strmap = \f -> fix (\g xs -> 
                   case unfold xs of
                   | Cons x xs' -> cons (f x) (\\(af : k) -> g [af] (xs' [af]))
                 ).

  nats : forall (k : Clock). Stream k Int.
  nats = fix (\g -> cons 0 (\\(af : k) -> strmap (\x -> x + 1) (g [af]))).

  data CoStream a = Cos (forall (k : Clock). Stream k a).
  conats : CoStream Int.
  conats = Cos (fix (\g -> cons 0 (\\(af : k) -> strmap (\x -> x + 1) (g [af])))).

  nats' : forall (k : Clock). Stream k Int.
  nats' = 
    let f = fix (\g n -> cons n (\\(af : k) -> g [af] (n + 1)))
    in  f 0.
|]