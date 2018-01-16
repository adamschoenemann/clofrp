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

module EveryOther (trans, exec) where

import Prelude hiding (fst, snd, map, pure, min, cos)
import Data.Functor.Classes

import CloFRP.Compiler
import CloFRP.QuasiQuoter

trans = undefined
exec = undefined

-- [hsclofrp|
--   data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
--   type Stream (k : Clock) a = Fix (StreamF k a).
--   data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

--   cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
--   cos = \x xs -> 
--     Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

--   uncos : forall (k : Clock) a. CoStream a -> Stream k a.
--   uncos = \xs -> case xs of | Cos xs' -> xs'.

--   cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
--   cons = \x xs -> fold (Cons x xs).

--   hdk : forall (k : Clock) a. Stream k a -> a.
--   hdk = \xs ->
--     case unfold xs of
--     | Cons x xs' -> x.

--   tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
--   tlk = \xs ->
--     case unfold xs of
--     | Cons x xs' -> xs'.

--   hd : forall a. CoStream a -> a.
--   hd = \xs -> hdk {K0} (uncos xs).
  
--   tl : forall a. CoStream a -> CoStream a.
--   tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

--   eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
--   eof = \f xs -> 
--     let tl2 = tl (tl xs) in
--     let dtl = (\\(af : k) -> (f [af]) tl2) in
--     cos (hd xs) dtl.

--   eo : forall a. CoStream a -> CoStream a.
--   eo = fix eof.
-- |]

-- exec :: [Bool]
-- exec = 
--   let tf = True : False : tf
--   in  stream2lst . uncos . eo $ Cos (lst2stream tf)

-- trans :: forall a. [a] -> [a]
-- trans xs = stream2lst . uncos . eo $ Cos (lst2stream xs)

-- stream2lst :: Stream k a -> [a]
-- stream2lst (Fold (Cons x xs)) = x : stream2lst (xs ())

-- lst2stream :: [a] -> Stream k a
-- lst2stream []       = error "lst2stream on empty list"
-- lst2stream (x : xs) = Fold (Cons x (const $ lst2stream xs))