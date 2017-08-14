{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.Annotated where

import Text.Parsec.Pos
import Data.Data

data Annotated a t = A a t
  deriving (Show, Eq, Data, Typeable)

unann :: Annotated a t -> t
unann (A _ x) = x


type Located t = Annotated t SourcePos