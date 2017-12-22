{-# OPTIONS_GHC -fno-warn-orphans #-}

module CloFRP.AST.Utils where

import CloFRP.Annotated
import Text.Parsec (SourcePos)
import CloFRP.Pretty
import Data.String (fromString)

instance Pretty (SourcePos) where
  pretty = fromString . show

-- collect :: (Type' a s -> Maybe (n, Type a s)) -> Type a s -> ([n], Type a s)
collect :: (f -> Maybe (n, Annotated a f)) -> Annotated a f -> ([n], Annotated a f)
collect p (A ann ty')
  | Just (n, t) <- p ty' = 
      let (ns, t') = collect p t
      in  (n:ns, t')
  | otherwise            = ([], A ann ty')
