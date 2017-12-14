{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.Examples where

import CloFRP.Interop
import CloFRP.QuasiQuoter
import Text.Parsec.Pos

type CTStream = 'CTFree "Stream" :@: 'CTFree "K0"
type CTNat = 'CTFree "Nat"

clott_add :: CloFRP (CTStream :@: CTTuple [CTNat, CTNat] :->: CTStream :@: CTNat) SourcePos
clott_add = [clott|
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