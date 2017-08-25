{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeApplications #-}

module Fixtures where

import CloTT.QuasiQuoter

import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Decl as P
import qualified CloTT.Parser.Prog as P

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
