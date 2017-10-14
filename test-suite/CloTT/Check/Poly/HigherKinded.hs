{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.Poly.HigherKinded where

import Test.Tasty.Hspec

import           CloTT.Check.Poly.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Check.Poly.Prog
import           CloTT.AST.Name


higherKindedSpec :: Spec
higherKindedSpec = do
  describe "functors!" $ do
    it "works" $ do
      let prog = [unsafeProg|
        data Functor (f : * -> *) = Functor (forall a b. (a -> b) -> f a -> f b).
        data Id a = Id a.
        data Maybe a = Nothing | Just a.
        data List a = Nil | Cons a (List a).

        idf : Functor Id.
        idf = Functor (\f x -> case x of
                | Id x' -> Id (f x')                
              ).
        
        fmapMaybe : forall a b. (a -> b) -> Maybe a -> Maybe b.
        fmapMaybe = \f x -> case x of
          | Nothing -> Nothing
          | Just x' -> Nothing.
        
        maybef : Functor Maybe.
        maybef = Functor fmapMaybe.

        -- we use general recursion here. Soon, we cannot do this
        fmapList : forall a b. (a -> b) -> List a -> List b.
        fmapList = \f xs -> case xs of
          | Nil -> Nil
          | Cons x xs' -> Cons (f x) (fmapList f xs).

        listf : Functor List.
        listf = Functor fmapList.
        
      |]
      runCheckProg mempty prog `shouldYield` ()