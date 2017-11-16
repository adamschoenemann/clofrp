{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}

module CloTT.AST.Helpers where

import CloTT.Annotated
import CloTT.AST.Expr
import CloTT.AST.Type
import CloTT.AST.Name
import CloTT.AST.Pat
import CloTT.AST.Kind
import CloTT.AST.Prim (Prim)
import qualified CloTT.AST.Prim as P

app :: (?annotation :: a) => Expr a -> Expr a -> Expr a
app x y = A ?annotation $ x `App` y

tapp :: (?annotation :: a) => Type a Poly -> Type a Poly -> Type a Poly
tapp x y = A ?annotation $ x `TApp` y

prim :: (?annotation :: a) => Prim -> Expr a
prim = A ?annotation . Prim

var :: (?annotation :: a) => Name -> Expr a
var = A ?annotation . Var

tvar :: (?annotation :: a) => Name -> Type a Poly
tvar = A ?annotation . TVar

tfree :: (?annotation :: a) => Name -> Type a Poly
tfree = A ?annotation . TFree

lam :: (?annotation :: a) => Name -> Maybe (Type a Poly) -> Expr a -> Expr a
lam n t e = A ?annotation $ Lam n t e

tuple :: (?annotation :: a) => [Expr a] -> Expr a
tuple = A ?annotation . Tuple

casee :: (?annotation :: a) => Expr a -> [(Pat a, Expr a)] -> Expr a
casee e = A ?annotation . Case e

bind :: (?annotation :: a) => Name -> Pat a
bind = A ?annotation . Bind

match :: (?annotation :: a) => Name -> [Pat a] -> Pat a
match ps = A ?annotation . Match ps

tickvar :: (?annotation :: a) => Name -> Expr a
tickvar = A ?annotation . TickVar

tAbs :: (?annotation :: a) => Name -> Name -> Expr a -> Expr a
tAbs af k = A ?annotation . TickAbs af k

forAll :: (?annotation :: a) => [Name] -> Type a Poly -> Type a Poly
forAll nms t = foldr fn t $ nms where
  fn nm acc = A ?annotation $ Forall nm Star acc

infixr 1 `arr`
arr :: (?annotation :: a) => Type a Poly -> Type a Poly -> Type a Poly
arr x y = A ?annotation $ x :->: y