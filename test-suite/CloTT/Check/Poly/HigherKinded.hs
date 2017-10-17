{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloTT.Check.Poly.HigherKinded where

import Test.Tasty.Hspec

import           CloTT.Check.Poly.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Check.Poly.Prog
import           CloTT.AST.Name

data State s a = State (s -> (a, s))

-- foo :: forall s a b. State s a -> State s b
-- foo (State sfn) =
--   State $ \s -> 
--     case sfn s of
--       (r, s') -> (r, s')


higherKindedSpec :: Spec
higherKindedSpec = do
  describe "functors!" $ do
    it "works" $ do
      let prog = [unsafeProg|
        type Fmap (f : * -> *) = forall a b. (a -> b) -> f a -> f b.
        data Functor (f : * -> *) = Functor (Fmap f).
        data Id a = Id a.
        data Maybe a = Nothing | Just a.
        data List a = Nil | Cons a (List a).
        data Pair a b = Pair a b.

        fmap : forall (f : * -> *). Functor f -> Fmap f.
        fmap = \x -> case x of
          | Functor fmap' -> fmap'.

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

        fmapPair : forall a b c. (b -> c) -> Pair a b -> Pair a c.
        fmapPair = \f p -> case p of
          | Pair x y -> Pair x (f y).
        
        pairf : forall a. Functor (Pair a).
        pairf = Functor fmapPair.

        fmapListMaybe : forall a b. (a -> b) -> List (Maybe a) -> List (Maybe b).
        fmapListMaybe = \f xs -> (fmap listf) (fmap maybef f) xs.
        
      |]
      runCheckProg mempty prog `shouldYield` ()

  describe "bi-functors!" $ do
    it "works" $ do
      let prog = [unsafeProg|
        type Bimap (f : * -> * -> *) = forall a b c d. (a -> c) -> (b -> d) -> f a b -> f c d.
        data Bifunctor (f : * -> * -> *) = Bifunctor (Bimap f).

        bimap : forall (f : * -> * -> *). Bifunctor f -> Bimap f.
        bimap = \f -> case f of
          | Bifunctor bimap' -> bimap'.

        data Pair a b = Pair a b.

        first : forall (f : * -> * -> *) a b c. Bifunctor f -> (a -> c) -> f a b -> f c b.
        first = \f fn -> bimap f fn (\x -> x).

        second : forall (f : * -> * -> *) a b c. Bifunctor f -> (b -> c) -> f a b -> f a c.
        second = \f fn -> bimap f (\x -> x) fn.

        bimapPair : forall a b c d. (a -> c) -> (b -> d) -> Pair a b -> Pair c d.
        bimapPair = \f g p -> case p of
          | Pair x y -> Pair (f x) (g y).
        
        pairbf : Bifunctor Pair.
        pairbf = Bifunctor bimapPair.

        data Bool = True | False.
        data A = A.
        data B = B.
        data Either a b = Left a | Right b.

        foo : Pair Bool Bool -> Pair (Either A B) Bool.
        foo = \p -> first pairbf (\x -> case x of | True -> Left A | False -> Right B) p.
      |]
      runCheckProg mempty prog `shouldYield` ()

  describe "pro-functors!" $ do
    it "works" $ do
      let prog = [unsafeProg|
        -- first arg is contravariant and second is covariant
        data Profunctor (f : * -> * -> *) =
          Profunctor (forall a b c d. (a -> b) -> (c -> d) -> f b c -> f a d).
        data Arr a b = Arr (a -> b).

        compose : forall a b c. (b -> c) -> (a -> b) -> a -> c.
        compose = \g f x -> g (f x).

        dimapArr : forall a b c d. (a -> b) -> (c -> d) -> Arr b c -> Arr a d.
        dimapArr = \f g arr -> case arr of
          | Arr h -> Arr (compose g (compose h f)).

        pairf : Profunctor Arr.
        pairf = Profunctor dimapArr.
      |]
      runCheckProg mempty prog `shouldYield` ()
  
  describe "monads!" $ do
    it "works" $ do
      let prog = [unsafeProg|
        data Monad (m : * -> *) =
          Monad (forall a. a -> m a) (forall a b. (a -> m b) -> m a -> m b).
        
        data Maybe a = Nothing | Just a.

        maybeM : Monad Maybe.
        maybeM = Monad
          Just
          (\fn x -> case x of
            | Nothing -> Nothing
            | Just x' -> fn x'
          ).
        
        data State s a = State (s -> (a, s)).
        data Bool = True | False.

        -- really annoying without let bindings
        stateM : forall s. Monad (State s).
        stateM = Monad
          (\x -> State (\s -> (x, s)))
          (\fn x -> case x of 
            | State sfn -> State (\s -> case sfn s of
              | (r, s') -> case fn r of
                | State sfn' -> sfn' s'
            )
          ).

      |]
      -- shouldFail $ runCheckProg mempty prog 
      runCheckProg mempty prog `shouldYield` ()