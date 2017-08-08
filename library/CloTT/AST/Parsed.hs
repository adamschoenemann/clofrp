{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module CloTT.AST.Parsed ( 
  module CloTT.AST.Parsed,
  P.Prim(..)
) where

import CloTT.Annotated
import CloTT.AST.Name
import qualified CloTT.AST.Prim as P

type Expr a = Annotated a (Expr' a)

data Expr' a
  = Var Name
  | Lam Name (Expr a)
  | App (Expr a) (Expr a)
  | Tuple (Expr a) (Expr a)
  | Prim P.Prim
  deriving (Show, Eq)

unann :: Expr a -> Expr ()
unann (A _ expr) = A () (unannE expr) where
  unannE = \case
    Var nm -> Var nm
    Lam nm e -> Lam nm (unann e)
    App e1 e2 -> App (unann e1) (unann e2)
    Tuple e1 e2 -> Tuple (unann e1) (unann e2)
    Prim p -> Prim p

infix 9 ~=~
(~=~) :: Expr a -> Expr b -> Bool
e1 ~=~ e2 = unann e1 == unann e2