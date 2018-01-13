{-# OPTIONS_GHC -ddump-splices #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloFRP.CompilerSpec where

import Prelude hiding (negate)
import Test.Tasty.Hspec
import CloFRP.QuasiQuoter
import CloFRP.Compiler
import Data.Function (fix)
import CloFRP.Examples
import qualified CloFRP.Fixtures.Imp1 as Imp1


strmap' :: (a -> b) -> Stream k a -> Stream k b
strmap' f (Fold (Cons x xs)) = Fold (Cons (f x) (\_ -> strmap' f (xs ())))

listmap :: (a -> b) -> List a -> List b
listmap f (Fold l) = Fold $
  case l of
    Nil -> Nil
    LCons x xs -> LCons (f x) (listmap f xs)

listnats :: List Int
listnats = fix (\g -> Fold (LCons 0 (listmap (+1) g)))

listtake :: Int -> List a -> [a]
listtake _ (Fold Nil) = []
listtake n (Fold (LCons x xs))
  | n <= 0    = []
  | otherwise = x : listtake (n-1) xs

hasknats :: Stream k Int
hasknats = Fold (Cons 0 (\_ -> strmap' (+1) hasknats))
-- hasknats = gfix (\g -> Fold (Cons 0 (\_ -> strmap' (+1) $ g ())))

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
      let n = 10000
      strtake n (strconst 1) `shouldBe` replicate n (1 :: Int)
    specify "nats" $ do
      let n = 2000
      -- strtake n nats `shouldBe` [0..(n-1)]
      strtake n hasknats `shouldBe` [0..(n-1)]
      -- listtake n listnats `shouldBe` [0..(n-1)]

