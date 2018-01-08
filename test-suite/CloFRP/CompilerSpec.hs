{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.CompilerSpec where

import Prelude hiding (negate)
import Test.Tasty.Hspec
import CloFRP.Compiler
import CloFRP.QuasiQuoter


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

  nats' : forall (k : Clock). Stream k Int.
  nats' = 
    let f = fix (\g n -> cons n (\\(af : k) -> g [af] (n + 1)))
    in  f 0.
|]

strtake :: Int -> Stream k a -> [a]
strtake n (Fold (Cons x xs))
  | n <= 0    = []
  | otherwise = x : strtake (n-1) (xs ())

compilerSpec :: Spec
compilerSpec = do
  describe "compiler expressions" $ do
    it "works with id function" $ do
      [hsclofrp| \x -> x |] True `shouldBe` True
    it "works with literals" $ do
      [hsclofrp| 10 |] `shouldBe` (10 :: Integer)
    it "works with tick-abstractions" $ do
      [hsclofrp| \\(af : k) -> 10 |] () `shouldBe` (10 :: Integer)
    it "works with multi-param lambdas" $ do
      [hsclofrp| \x y -> x |] 10 () `shouldBe` (10 :: Integer)
  describe "compiler declarations" $ do
    specify "cfp_id" $ do
      cfp_id True `shouldBe` True
      cfp_id () `shouldBe` ()
    specify "negate" $ do
      negate True `shouldBe` False
      negate False `shouldBe` True
    specify "toInt" $ do
      toInt five `shouldBe` 5
    specify "strconst" $ do
      strtake 100 (strconst 1) `shouldBe` replicate 100 (1 :: Int)
    specify "nats" $ do
      let n = 2000
      strtake n nats `shouldBe` [0..(n-1)]
