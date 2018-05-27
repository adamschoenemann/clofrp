{-# OPTIONS_GHC -fno-warn-orphans #-}

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

module CloFRP.InteropSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.String (fromString)
import NeatInterpolation
import Data.Proxy
import Text.Parsec.Pos (SourcePos)

import qualified CloFRP.AST  as E
import qualified CloFRP.AST.Prim    as P
import           CloFRP.AST ((@->:), (@@:), Kind(..))
import           CloFRP.AST (LamCalc(..))
import qualified Fixtures

import qualified Data.Map.Strict as M
import           CloFRP.QuasiQuoter
import           CloFRP.TestUtils
import           CloFRP.Pretty
import           CloFRP.Eval
import           CloFRP.Annotated (unann, Annotated(..))
import           CloFRP.Interop

instance ToHask ('CTFree "Bool") Bool where
  toHask (SFree px) (Constr "True" [])  = True
  toHask (SFree px) (Constr "False" []) = False
  toHask (SFree px) v                   = error ("Expected Cons but got " ++ pps (takeConstr 2 v))

instance ToCloFRP Bool ('CTFree "Bool") where
  toCloFRP (SFree px) True  = (Constr "True" [])  
  toCloFRP (SFree px) False = (Constr "False" []) 
  -- toCloFRP (SFree px) _                   = undefined

-- data Nat = Z | S Nat deriving (Show, Eq)

-- five :: Nat
-- five = S (S (S (S (S Z))))

-- plus :: Nat -> Nat -> Nat
-- plus Z n = n
-- plus (S m) n = S (plus m n)

instance ToHask ('CTFree "Nat") Int where
  toHask (SFree px) (Fold (Constr "Z" []))  = 0
  toHask (SFree px) (Fold (Constr "S" [r])) = succ (toHask (SFree px) r)
  toHask (SFree px) _                = undefined

instance ToCloFRP Int ('CTFree "Nat") where
  toCloFRP (SFree px) 0 = Fold (Constr "Z" [])
  toCloFRP (SFree px) n = Fold (Constr "S" [toCloFRP (SFree px) (n-1)])
  -- toCloFRP (SFree px) _                = undefined

instance ToHask t r => ToHask ('CTFree "Stream" :@: u :@: t) [r] where
  toHask s@((s1 `SApp` s2) `SApp` s3) (Fold (Constr "Cons" [v, c])) = toHask s3 v : toHask s c
  toHask s@((s1 `SApp` s2) `SApp` s3) v = error ("Expected fold (Cons x ..) but got " ++ pps (takeConstr 2 v))

data Wrap a = Wrap a
data Foo a = Foo (Wrap a)

instance ToCloFRP h c => ToCloFRP (Wrap h) ('CTFree "Wrap" :@: c) where
  toCloFRP (s1 `SApp` s2) (Wrap x) = Constr "Wrap" [toCloFRP s2 x]

instance ToCloFRP h c => ToCloFRP (Foo h) ('CTFree "Foo" :@: c) where
  toCloFRP (s1 `SApp` s2) (Foo x) = Constr "Foo" [toCloFRP (SFree (Proxy @"Wrap") `SApp` s2) x]

-- haskell lists to clott streams over k₀
instance ToCloFRP hask clott => ToCloFRP [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) where
  toCloFRP s@(s1 `SApp` s2) xs = clottStream xs where
    clottStream (x : xs') = Fold (Constr "Cons" [toCloFRP s2 x, Delay (clottStream xs')])
    clottStream []        = runtimeErr "End of stream"

-- haskell lists to clott coinductive streams 
instance ToCloFRP [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) => ToCloFRP [hask] ('CTFree "CoStream" :@: clott) where
  toCloFRP s@(s1 `SApp` s2) xs = 
    let strsing = SFree (Proxy @"Stream") `SApp` SFree (Proxy @"K0") `SApp` s2
    in  Constr "Cos" [toCloFRP strsing xs] where

type CTStream = 'CTFree "Stream" :@: 'CTFree "K0"
type CTNat = 'CTFree "Nat"

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
      end
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
        end
      end
    ).
|]

addition_ex :: IO ()
addition_ex = interact (unlines . process . lines) where
  process = map (("result: " ++) . (show :: Int -> String)) . streamTrans clott_add .
            map (read :: String -> (Int,Int))


interopSpec :: Spec
interopSpec = do
  describe "execute" $ do
    it "works with bool" $ do
      let prog = [clofrp|
        data Bool = True | False.
        main : Bool.
        main = True.
      |]
      execute prog `shouldBe` True

    it "works with nats" $ do
      let prog = [clofrp|
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
    
    -- it "it works for every-other" $ do
    --   let prog = [clofrp|
    --     data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
    --     type Stream (k : Clock) a = Fix (StreamF k a).
    --     data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

    --     cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
    --     cos = \x xs -> 
    --       Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

    --     uncos : forall (k : Clock) a. CoStream a -> Stream k a.
    --     uncos = \xs -> case xs of | Cos xs' -> xs'.

    --     cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
    --     cons = \x xs -> fold (Cons x xs).

    --     hdk : forall (k : Clock) a. Stream k a -> a.
    --     hdk = \xs ->
    --       case unfold xs of
    --       | Cons x xs' -> x.

    --     tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
    --     tlk = \xs ->
    --       case unfold xs of
    --       | Cons x xs' -> xs'.

    --     hd : forall a. CoStream a -> a.
    --     hd = \xs -> hdk {K0} (uncos xs).
        
    --     tl : forall a. CoStream a -> CoStream a.
    --     tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

    --     eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
    --     eof = \f xs -> 
    --       let tl2 = tl (tl xs) in
    --       let dtl = (\\(af : k) -> (f [af]) tl2) in
    --       cos (hd xs) dtl.

    --     eo : forall a. CoStream a -> CoStream a.
    --     eo = fix eof.

    --     data Bool = True | False.        
    --     truefalse : forall (k : Clock). Stream k Bool.
    --     truefalse = fix (\g -> cons True (\\(af : k) -> cons False g)).

    --     main : Stream K0 Bool.
    --     main = 
    --       let Cos xs = eo (Cos truefalse) in
    --       xs.
    --   |]
    --   take 10 (execute prog) `shouldBe` replicate 10 True

  describe "transform" $ do
    it "works with Bool -> Bool" $ do
      let prog = [clofrp|
        data Bool = True | False.
        main : Bool -> Bool.
        main = \x -> 
          case x of
          | True -> False
          | False -> True
          end.
      |]
      transform prog False `shouldBe` True

    it "works with double (Nat)" $ do
      let prog = [clofrp|
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
            end
          in  primRec {NatF} body m.

        main : Nat -> Nat.
        main = \x -> plus x x.
      |]
      transform prog 5 `shouldBe` 10
    
    it "works with wrapped types" $ do
      let prog = [clofrp|
        data Wrap a = Wrap a deriving Functor.
        data Foo a = Foo (Wrap a) deriving Functor.
        data Bool = True | False.
        main : Foo Bool -> Bool.
        main = \x ->
          case x of
          | Foo (Wrap b) -> b
          end.
      |]
      transform prog (Foo (Wrap True)) `shouldBe` True
    
    it "works with tuples (1)" $ do
      let prog = [clofrp|
        data Bool = True | False.
        main : Bool -> (Bool, Bool).
        main = \x -> (x, x).
      |]
      transform prog True `shouldBe` (True, True)

    it "works with tuples (2)" $ do
      let prog = [clofrp|
        data Bool = True | False.
        main : Bool -> (Bool, Bool, Bool).
        main = \x -> (x, x, x).
      |]
      transform prog True `shouldBe` (True, True, True)
    
    it "works with fixpoint (1)" $ do
      let prog = [clofrp|
        data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
        type Stream (k : Clock) a = Fix (StreamF k a).
        data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).
        data Bool = True | False.        

        negate : forall (k : Clock). Stream k Bool -> Stream k Bool.
        negate = fix (\g xs ->
          case unfold xs of 
          | Cons x xs'-> 
            let x' = (case x of | True -> False | False -> True end) : Bool
            in  fold (Cons x' (\\(af : k) -> (g [af]) (xs' [af])))
          end
        ).

        -- fixid : forall (k : Clock) a. Stream k a -> Stream k a.
        -- fixid = fix (\g xs -> 
        --   case unfold xs of
        --   | Cons x xs' -> fold (Cons x (\\(af : k) -> g [af] (xs' [af])))
        -- )

        main : Stream K0 Bool -> Stream K0 Bool.
        main = \xs -> negate xs.
      |]
      let n = 10
      let falses = repeat False
      take n (streamTrans prog falses) `shouldBe` replicate n True

    it "works with clott_add" $ do
      let n = 50
      let inputs = zip [1..] [2..]
      let output = take n (streamTrans clott_add inputs)
      let expected = take n $ map (uncurry (+)) inputs :: [Int]
      output `shouldBe` expected

    -- it "it works for every-other" $ do
    --   let prog = [clofrp|
    --     data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
    --     type Stream (k : Clock) a = Fix (StreamF k a).
    --     data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

    --     cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
    --     cos = \x xs -> 
    --       Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

    --     uncos : forall (k : Clock) a. CoStream a -> Stream k a.
    --     uncos = \xs -> case xs of | Cos xs' -> xs'.

    --     cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
    --     cons = \x xs -> fold (Cons x xs).

    --     hdk : forall (k : Clock) a. Stream k a -> a.
    --     hdk = \xs ->
    --       case unfold xs of
    --       | Cons x xs' -> x.

    --     tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
    --     tlk = \xs ->
    --       case unfold xs of
    --       | Cons x xs' -> xs'.

    --     hd : forall a. CoStream a -> a.
    --     hd = \xs -> hdk {K0} (uncos xs).
        
    --     tl : forall a. CoStream a -> CoStream a.
    --     tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

    --     eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
    --     eof = \f xs -> 
    --       let tl2 = tl (tl xs) in
    --       let dtl = (\\(af : k) -> (f [af]) tl2) in
    --       cos (hd xs) dtl.

    --     eo : forall a. CoStream a -> CoStream a.
    --     eo = fix eof.

    --     data Bool = True | False.

    --     main : CoStream Bool -> Stream K0 Bool.
    --     main = \input ->
    --       let Cos xs = eo input in
    --       xs.
    --   |]
    --   let n = 10
    --   let truefalse = (True : False : truefalse :: [Bool])
    --   -- putStrLn . show $ take n (transform prog truefalse :: [Bool])
    --   -- putStrLn . show $ take n (repeat True)
    --   take n (transform prog truefalse) `shouldBe` replicate n True
