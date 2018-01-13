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
{-# LANGUAGE ImpredicativeTypes #-}

module CloFRP.Fixtures.Imp1 where

import Prelude hiding (id)
import CloFRP.Compiler
import CloFRP.QuasiQuoter

[hsclofrp|
  id : forall a. a -> a.
  id = \x -> x.

  pred : forall a. a -> a.
  pred = id id.

  imp : (forall a. a -> a) -> (forall a. a -> a).
  imp = id {forall a. a -> a}.

  imp2 : forall a. a -> a.
  imp2 = imp id.

  extern data Maybe a = Nothing | Just a.

  imp3 : Maybe (forall a. a -> a).
  imp3 = Just {forall a. a -> a} id.

  def : forall a. a -> Maybe a -> a.
  def = \def m ->
    case m of
    | Nothing -> def
    | Just x -> x.
  
  -- explicit type app is required here by Haskell, but not by CloFRP
  imp4 : Maybe (forall a. a -> a) -> forall a. a -> a.
  imp4 = \x -> def {forall a. a -> a} id x.

  imp4eta : Maybe (forall a. a -> a) -> forall a. a -> a.
  imp4eta = def {forall a. a -> a} id.
|]