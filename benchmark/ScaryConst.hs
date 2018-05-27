{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module ScaryConst (main) where

import Prelude hiding (fst, snd, pure, min, cos, const)
import Data.Functor.Classes

import CloFRP.Compiler
import CloFRP.QuasiQuoter

[hsclofrp|
  data StreamF (k : Clock) a f = Cons a (|>k f).
  type Stream (k : Clock) a = Fix (StreamF k a).

  cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
  cons = \x xs -> fold (Cons x xs).

  const : forall (k : Clock) a. a -> Stream k a.
  const = \x -> fix (\g -> cons x g).

  strmap : forall (k : Clock) a b. (a -> b) -> Stream k a -> Stream k b.
  strmap = \f -> 
    let mapfix = \g xs ->
          case unfold xs of
          | Cons x xs' -> cons (f x) (\\(af : k) -> g [af] (xs' [af]))
          end
    in fix mapfix.

  nats : forall (k : Clock). Int -> Stream k Int.
  nats = fix (\g n -> cons n (\\(af : k) -> g [af] (n + 1))).

  scary : Stream K0 (Stream K0 Int).
  scary = const (nats 0).
|]

stream2lst :: Stream k a -> [a]
stream2lst (Fold (Cons x xs)) = x : stream2lst (xs ())

main :: [[Int]]
main = map stream2lst $ stream2lst scary
