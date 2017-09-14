{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}

module CloTT.Annotated where

import Text.Parsec.Pos
import Data.Data

data Annotated a t = A a t
  deriving (Show, Eq, Data, Typeable)


type Located t = Annotated t SourcePos

-- terrible :O
class Eq b => Unann a b | a -> b where
  unann :: a -> b
  (=%=) :: a -> a -> Bool
  x =%= y = unann x == unann y

