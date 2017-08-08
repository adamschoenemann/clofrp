module CloTT.Annotated where

import Text.Parsec.Pos

data Annotated a t = A a t
  deriving (Show, Eq)


type Located t = Annotated t SourcePos