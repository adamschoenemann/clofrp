{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstrainedClassMethods #-}

module CloTT.Context where

class Monoid a => Context a where
  type Key a
  type Elem a
  extend  :: Key a -> Elem a -> a -> a
  isMemberOf  :: Key a -> a -> Bool
  query :: Key a -> a -> Maybe (Elem a)
  isEmpty :: Eq a => a -> Bool
  isEmpty x = x == mempty