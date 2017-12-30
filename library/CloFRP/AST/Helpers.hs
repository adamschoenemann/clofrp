{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.AST.Helpers where

import CloFRP.Annotated
import CloFRP.AST.Expr
import CloFRP.AST.Type
import CloFRP.AST.Name
import CloFRP.AST.Pat
import CloFRP.AST.Kind
import CloFRP.AST.Prim (Prim)
import qualified CloFRP.AST.Prim as P

app :: (?annotation :: a) => Expr a -> Expr a -> Expr a
app x y = A ?annotation $ x `App` y

tapp :: (?annotation :: a) => PolyType a -> PolyType a -> PolyType a
tapp x y = A ?annotation $ x `TApp` y

prim :: (?annotation :: a) => Prim -> Expr a
prim = A ?annotation . Prim

var :: (?annotation :: a) => Name -> Expr a
var = A ?annotation . Var

tvar :: (?annotation :: a) => Name -> PolyType a
tvar = A ?annotation . TVar

tfree :: (?annotation :: a) => Name -> PolyType a
tfree = A ?annotation . TFree

lam :: (?annotation :: a) => Name -> Maybe (PolyType a) -> Expr a -> Expr a
lam n t e = A ?annotation $ Lam n t e

lam' :: (?annotation :: a) => Name -> Expr a -> Expr a
lam' n e = A ?annotation $ Lam n Nothing e

tuple :: (?annotation :: a) => [Expr a] -> Expr a
tuple = A ?annotation . Tuple

ttuple :: (?annotation :: a) => [PolyType a] -> PolyType a
ttuple = A ?annotation . TTuple

casee :: (?annotation :: a) => Expr a -> [(Pat a, Expr a)] -> Expr a
casee e = A ?annotation . Case e

bind :: (?annotation :: a) => Name -> Pat a
bind = A ?annotation . Bind

match :: (?annotation :: a) => Name -> [Pat a] -> Pat a
match ps = A ?annotation . Match ps

ptuple :: (?annotation :: a) => [Pat a] -> Pat a
ptuple = A ?annotation . PTuple

tickvar :: (?annotation :: a) => Name -> Expr a
tickvar = A ?annotation . TickVar

tAbs :: (?annotation :: a) => Name -> Name -> Expr a -> Expr a
tAbs af k = A ?annotation . TickAbs af k

forAll :: (?annotation :: a) => [Name] -> PolyType a -> PolyType a
forAll nms t = foldr fn t $ nms where
  fn nm acc = A ?annotation $ Forall nm Star acc

forAllK :: (?annotation :: a) => [(Name, Kind)] -> PolyType a -> PolyType a
forAllK nms t = foldr fn t $ nms where
  fn (nm, k) acc = A ?annotation $ Forall nm k acc

infixr 1 `arr`
arr :: (?annotation :: a) => PolyType a -> PolyType a -> PolyType a
arr x y = A ?annotation $ x :->: y

primRec :: (?annotation :: a) => PolyType a -> Expr a
primRec = A ?annotation . PrimRec

fmapE :: (?annotation :: a) => PolyType a -> Expr a
fmapE = A ?annotation . Fmap

fixE :: (?annotation :: a) => Expr a
fixE = A ?annotation $ Prim P.Fix

foldE :: (?annotation :: a) => Expr a
foldE = A ?annotation $ Prim P.Fold

unfoldE :: (?annotation :: a) => Expr a
unfoldE = A ?annotation $ Prim P.Unfold

later :: (?annotation :: a) => PolyType a -> PolyType a -> PolyType a
later kappa ty = A ?annotation $ Later kappa ty

exists :: (?annotation :: a) => Name -> PolyType a
exists nm = A ?annotation $ TExists nm

letE :: (?annotation :: a) => Pat a -> Expr a -> Expr a -> Expr a
letE nm e1 e2 = A ?annotation $ Let nm e1 e2