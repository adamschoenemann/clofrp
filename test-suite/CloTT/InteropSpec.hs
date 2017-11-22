{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module CloTT.InteropSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.String (fromString)
import NeatInterpolation
import Debug.Trace

import qualified CloTT.AST.Parsed  as E
import qualified CloTT.AST.Prim    as P
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import qualified Fixtures

import qualified Data.Map.Strict as M
import           CloTT.QuasiQuoter
import           CloTT.TestUtils
import           CloTT.Pretty
import           CloTT.Eval
import           CloTT.Annotated (unann, Annotated(..))
import           CloTT.Interop

instance ToHask ('CTFree "Bool") Bool where
  toHask (SFree px) (Constr "True" [])  = True
  toHask (SFree px) (Constr "False" []) = False
  toHask (SFree px) _                   = undefined

data Nat = Z | S Nat deriving (Show, Eq)
five = S (S (S (S (S Z))))

instance ToHask ('CTFree "Nat") Nat where
  toHask (SFree px) (Constr "Z" []) = Z
  toHask (SFree px) (Constr "S" [r]) = S (toHask (SFree px) r)
  toHask (SFree px) _                = undefined

instance ToHask t r => ToHask ('CTFree "Stream" :@: u :@: t) [r] where
  toHask s@((s1 `SApp` s2) `SApp` s3) (Constr "Cons" [v, c]) = toHask s3 v : toHask s c
  toHask s@((s1 `SApp` s2) `SApp` s3) _ = undefined

-- instance ToHask ('CTFree "Stream" :@: u :@: 'CTFree "Bool") [Bool] where
--   toHask s@((s1 `SApp` s2) `SApp` s3) (Constr "Cons" [v, c]) = toHask s3 v : toHask s c

interopSpec :: Spec
interopSpec = do
  describe "execute" $ do
    it "works with bool" $ do
      let prog = [clott|
        data Bool = True | False.
        main : Bool.
        main = True.
      |]
      execute prog `shouldBe` True

    it "works with nats" $ do
      let prog = [clott|
        data NatF f = Z | S f deriving Functor.
        type Nat = Fix (NatF).

        s : Nat -> Nat.
        s = \x -> fold (S x).

        z : Nat.
        z = fold Z.

        main : Nat.
        main = s (s (s (s (s z)))).
      |]
      execute prog `shouldBe` five
    
    it "it works for every-other" $ do
      let prog = [clott|
        data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
        type Stream (k : Clock) a = Fix (StreamF k a).
        data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

        cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
        cos = \x xs -> 
          Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

        uncos : forall (k : Clock) a. CoStream a -> Stream k a.
        uncos = \xs -> case xs of | Cos xs' -> xs'.

        cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
        cons = \x xs -> fold (Cons x xs).

        hdk : forall (k : Clock) a. Stream k a -> a.
        hdk = \xs ->
          case unfold xs of
          | Cons x xs' -> x.

        tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
        tlk = \xs ->
          case unfold xs of
          | Cons x xs' -> xs'.

        hd : forall a. CoStream a -> a.
        hd = \xs -> hdk {K0} (uncos xs).
        
        tl : forall a. CoStream a -> CoStream a.
        tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

        eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
        eof = \f xs -> 
          let tl2 = tl (tl xs) in
          let dtl = (\\(af : k) -> (f [af]) tl2) in
          cos (hd xs) dtl.

        eo : forall a. CoStream a -> CoStream a.
        eo = fix eof.

        data Bool = True | False.        
        truefalse : forall (k : Clock). Stream k Bool.
        truefalse = fix (\g -> cons True (\\(af : k) -> cons False g)).

        main : Stream K0 Bool.
        main = 
          let Cos xs = eo (Cos truefalse) in
          xs.
      |]
      take 10 (execute prog) `shouldBe` replicate 10 True
