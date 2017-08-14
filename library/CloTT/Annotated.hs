{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.Annotated where

import Text.Parsec.Pos
import Data.Data

data Annotated a t = A a t
  deriving (Show, Eq, Data, Typeable)


type Located t = Annotated t SourcePos