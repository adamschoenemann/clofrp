{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module CloTT.Annotated where

import Text.Parsec.Pos
import Data.Data
import Control.DeepSeq
import GHC.Generics

data Annotated a t = A a t
  deriving (Show, Eq, Data, Typeable, Generic, NFData)


type Located t = Annotated t SourcePos

-- terrible :O
class Eq b => Unann a b | a -> b where
  unann :: a -> b
  (=%=) :: a -> a -> Bool
  x =%= y = unann x == unann y
  (=/%=) :: a -> a -> Bool
  x =/%= y = unann x /= unann y

-- instance Unann a b => Unann (Either c a) (Either c b) where
--   unann (Right x) = Right (unann x)
--   unann x         = x