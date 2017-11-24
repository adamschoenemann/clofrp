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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloTT.InteropSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.String (fromString)
import NeatInterpolation
import Data.Proxy
import Text.Parsec.Pos (SourcePos)

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
  toHask (SFree px) v                   = error ("Expected Cons but got " ++ pps (takeConstr 2 v))

instance ToCloTT Bool ('CTFree "Bool") where
  toCloTT (SFree px) True  = (Constr "True" [])  
  toCloTT (SFree px) False = (Constr "False" []) 
  -- toCloTT (SFree px) _                   = undefined

-- data Nat = Z | S Nat deriving (Show, Eq)

-- five :: Nat
-- five = S (S (S (S (S Z))))

-- plus :: Nat -> Nat -> Nat
-- plus Z n = n
-- plus (S m) n = S (plus m n)

instance ToHask ('CTFree "Nat") Int where
  toHask (SFree px) (Constr "Z" [])  = 0
  toHask (SFree px) (Constr "S" [r]) = succ (toHask (SFree px) r)
  toHask (SFree px) _                = undefined

instance ToCloTT Int ('CTFree "Nat") where
  toCloTT (SFree px) 0 = Constr "Z" [] 
  toCloTT (SFree px) n = Constr "S" [toCloTT (SFree px) (n-1)] 
  -- toCloTT (SFree px) _                = undefined

instance ToHask t r => ToHask ('CTFree "Stream" :@: u :@: t) [r] where
  toHask s@((s1 `SApp` s2) `SApp` s3) (Constr "Cons" [v, c]) = toHask s3 v : toHask s c
  toHask s@((s1 `SApp` s2) `SApp` s3) v = error ("Expected Cons but got " ++ pps (takeConstr 2 v))

data Wrap a = Wrap a
data Foo a = Foo (Wrap a)

instance ToCloTT h c => ToCloTT (Wrap h) ('CTFree "Wrap" :@: c) where
  toCloTT (s1 `SApp` s2) (Wrap x) = Constr "Wrap" [toCloTT s2 x]

instance ToCloTT h c => ToCloTT (Foo h) ('CTFree "Foo" :@: c) where
  toCloTT (s1 `SApp` s2) (Foo x) = Constr "Foo" [toCloTT (SFree (Proxy @"Wrap") `SApp` s2) x]

-- haskell lists to clott streams over k₀
instance ToCloTT hask clott => ToCloTT [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) where
  toCloTT s@(s1 `SApp` s2) xs = clottStream xs where
    clottStream (x : xs') = Constr "Cons" [toCloTT s2 x, clottStream xs']
    clottStream []        = runtimeErr "End of stream"

-- haskell lists to clott coinductive streams 
instance ToCloTT [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) => ToCloTT [hask] ('CTFree "CoStream" :@: clott) where
  toCloTT s@(s1 `SApp` s2) xs = 
    let strsing = SFree (Proxy @"Stream") `SApp` SFree (Proxy @"K0") `SApp` s2
    in  Constr "Cos" [toCloTT strsing xs] where

instance (ToCloTT h1 c1, ToCloTT h2 c2) => ToCloTT (h1, h2) ('CTTuple [c1, c2]) where
  toCloTT (SPair s1 s2) (x1, x2) = Tuple [toCloTT s1 x1, toCloTT s2 x2]
  toCloTT (STup ss s)   (x1, x2) = error "impossible" -- Tuple [toCloTT s1 x1, toCloTT s2 x2]

instance (ToHask c1 h1, ToHask c2 h2) => ToHask ('CTTuple [c1, c2]) (h1, h2) where
  toHask (SPair s1 s2) (Tuple [x1, x2]) = (toHask s1 x1, toHask s2 x2)
  toHask (SPair s1 s2) v = error $ show $ "Expected tuple but got" <+> pretty v

-- cant make this inductive, since tuples are not inductive in haskell.
-- alternatively, one could marshall to HList instead which would allow it
instance (ToHask c1 h1, ToHask c2 h2, ToHask c3 h3) => ToHask ('CTTuple '[c1,c2,c3]) (h1,h2,h3) where
  toHask (s1 `STup` (s2 `SPair` s3)) (Tuple [x1,x2,x3]) = (toHask s1 x1, toHask s2 x2, toHask s3 x3)
  toHask (s1 `STup` (s2 `SPair` s3)) v = error $ show $ "Expected tuple but got" <+> pretty v


type CTStream = 'CTFree "Stream" :@: 'CTFree "K0"
type CTNat = 'CTFree "Nat"

clott_add :: CloTT (CTStream :@: CTTuple [CTNat, CTNat] :->: CTStream :@: CTNat) SourcePos
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

addition_ex :: IO ()
addition_ex = interact (unlines . process . lines) where
  process = map (("result: " ++) . (show :: Int -> String)) . transform clott_add .
            map (read :: String -> (Int,Int))


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
      execute prog `shouldBe` 5
    
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

  describe "transform" $ do
    it "works with Bool -> Bool" $ do
      let prog = [clott|
        data Bool = True | False.
        main : Bool -> Bool.
        main = \x -> 
          case x of
          | True -> False
          | False -> True.
      |]
      transform prog False `shouldBe` True

    it "works with double (Nat)" $ do
      let prog = [clott|
        data NatF f = Z | S f deriving Functor.
        type Nat = Fix (NatF).

        s : Nat -> Nat.
        s = \x -> fold (S x).

        z : Nat.
        z = fold Z.

        plus : Nat -> Nat -> Nat.
        plus = \m n -> 
          let body = \x ->
            case x of
              | Z -> n
              | S (m', r) -> s r
          in  primRec {NatF} body m.

        main : Nat -> Nat.
        main = \x -> plus x x.
      |]
      transform prog 5 `shouldBe` 10
    
    it "works with wrapped types" $ do
      let prog = [clott|
        data Wrap a = Wrap a deriving Functor.
        data Foo a = Foo (Wrap a) deriving Functor.
        data Bool = True | False.
        main : Foo Bool -> Bool.
        main = \x ->
          case x of
          | Foo (Wrap b) -> b.
      |]
      transform prog (Foo (Wrap True)) `shouldBe` True
    
    it "works with tuples (1)" $ do
      let prog = [clott|
        data Bool = True | False.
        main : Bool -> (Bool, Bool).
        main = \x -> (x, x).
      |]
      transform prog True `shouldBe` (True, True)

    it "works with tuples (2)" $ do
      let prog = [clott|
        data Bool = True | False.
        main : Bool -> (Bool, Bool, Bool).
        main = \x -> (x, x, x).
      |]
      transform prog True `shouldBe` (True, True, True)

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

        main : CoStream Bool -> Stream K0 Bool.
        main = \input ->
          let Cos xs = eo input in
          xs.
      |]
      let truefalse = True : False : truefalse :: [Bool]
      let n = 2000
      -- putStrLn . show $ take n (transform prog truefalse :: [Bool])
      -- putStrLn . show $ take n (repeat True)
      take n (transform prog truefalse) `shouldBe` replicate n True
