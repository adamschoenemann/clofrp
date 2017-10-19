{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module CloTT.AST.Parsed
  ( module CloTT.AST.Parsed
  , module CloTT.AST.Name
  , module CloTT.AST.Type
  , module CloTT.AST.Pat
  , module CloTT.AST.Expr
  , module CloTT.AST.Alias
  , module CloTT.AST.Kind
  , module CloTT.AST.Datatype
  , P.Prim(..)
  , Unann(..)
) where

import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import qualified CloTT.AST.Prim as P
import Data.Text.Prettyprint.Doc

import CloTT.Annotated 
import CloTT.AST.Name
import CloTT.AST.Type
import CloTT.AST.Pat
import CloTT.AST.Expr
import CloTT.AST.Alias
import CloTT.AST.Kind
import CloTT.AST.Datatype


type Decl a = Annotated a (Decl' a)
data Decl' a
  = FunD Name (Expr a)
  | DataD (Datatype a)
  | SigD Name (Type a Poly)
  | AliasD (Alias a)

instance Pretty (Decl a) where
  pretty (A _ d) = prettyD d where
    prettyD = \case
      FunD nm e  -> pretty nm <+> "=" <+> pretty e <> "."
      DataD dt   -> pretty dt <> "."
      SigD nm ty -> pretty nm <+> ":" <+> pretty ty <> "."
      AliasD al  -> pretty al <> "."

deriving instance Show a     => Show (Decl' a)
deriving instance Eq a       => Eq (Decl' a)
deriving instance Data a     => Data (Decl' a)
deriving instance Typeable a => Typeable (Decl' a)

data Prog a = Prog [Decl a]
  deriving (Show, Eq, Data, Typeable)

instance Pretty (Prog a) where
  pretty (Prog ds) = vsep $ map pretty ds

{-
data Nat = Z | S Nat

desugars to 
data NatF a = ZF | SF a
and 
type Nat = uX. NatF X.

So, we'll get
unfoldNat : Nat -> NatF Nat
which corresponds to a pattern match

and
Z : Nat
S : Nat -> Nat
which corresponds to a the original constructors

and primitive recursion over nats as 

plus : Nat -> Nat -> Nat
plus = \m n ->
  rec m of 
    | Z -> n
    | S m' with r -> S r.
-}

{-

data List a = Nil | Cons a (List a)

desugars to 
data ListF a x = Nil | Cons a x
type List a = uX. ListF a X.

constructors
Nil : forall a. List a
Cons : forall a. a -> List a -> List a

and patterns 
Nil : forall a. () -> a
Cons : forall a r. a -> List a -> r

we implement sum as

sum : List Nat -> Nat
sum = \xs ->
  rec xs of
    | Nil -> Z
    | Cons a xs with r -> plus a r.


-}

-- Here are some combinators for creating un-annotated expressions easily

var :: String -> Expr ()
var = A () . Var . UName

free :: Name -> Type () Poly
free nm = A () $ TFree nm

unit :: Expr ()
unit = A () . Prim $ P.Unit

nat :: Integer -> Expr ()
nat = A () . Prim . P.Nat

true :: Expr ()
true = A () . Var $ "True"

false :: Expr ()
false = A () . Var $ "False"

tup :: [Expr ()] -> Expr ()
tup = A () . Tuple

foldf :: Expr ()
foldf = A () . Prim $ P.Fold

unfoldf :: Expr ()
unfoldf = A () . Prim $ P.Unfold

the :: Type () Poly -> Expr () -> Expr ()
the t e = A () $ Ann e t

constr :: Name -> [Type () Poly] -> Constr ()
constr nm ts = A () $ Constr nm ts

datad :: Name -> [(Name, Kind)] -> [Constr ()] -> Decl ()
datad nm bs cs = A () $ DataD (Datatype nm bs cs)

fund :: Name -> Expr () -> Decl ()
fund nm e =  A () $ FunD nm e

sigd :: Name -> Type () Poly -> Decl ()
sigd nm t =  A () $ SigD nm t

aliasd :: Name -> [Name] -> Type () Poly -> Decl ()
aliasd nm bs t = A () $ AliasD (Alias nm (map (,Star) bs) t)

prog :: [Decl ()] -> Prog ()
prog = Prog

forAll :: [String] -> Type () Poly -> Type () Poly
forAll nms t = foldr fn t $ map UName nms where
  fn nm acc = A () $ Forall nm Star acc

clocks :: [String] -> Type () Poly -> Type () Poly
clocks nms t = foldr fn t $ map UName nms where
  fn nm acc = A () $ Clock nm acc

recTy :: Type () Poly -> Type () Poly
recTy t = A () $ RecTy t

tTup :: [Type () Poly] -> Type () Poly
tTup = A () . TTuple

exists :: Name -> Type () a
exists nm = A () $ TExists nm

caseof :: Expr () -> [(Pat (), Expr ())] -> Expr ()
caseof expr clauses = A () $ Case expr clauses

match :: Name -> [Pat ()] -> Pat ()
match nm ps = A () $ Match nm ps

pTup :: [Pat ()] -> Pat ()
pTup ps = A () $ PTuple ps

debrjn :: Integer -> Type () a
debrjn = A () . TVar . DeBruijn

tAbs :: (Name, Name) -> Expr () -> Expr ()
tAbs (a, k) e = A () $ TickAbs a k e

cAbs :: Name -> Expr () -> Expr ()
cAbs k e = A () $ ClockAbs k e

lete :: Pat () -> Expr () -> Expr () -> Expr ()
lete p e1 e2 = A () $ Let p e1 e2

later :: Name -> Type () Poly -> Type () Poly
later n t = A () $ Later n t


infixr 2 @->
infixr 2 @:->
infixl 8 @@
infixl 9 @::

class IsString a => LamCalc a t | a -> t where
  (@->) :: String -> a -> a
  (@:->) :: (String, t) -> a -> a
  (@@) :: a -> a -> a
  (@::) :: a -> t -> a


instance LamCalc (Expr ()) (Type () Poly) where
  nm @-> e = A () $ Lam (UName nm) Nothing e
  (nm, t) @:-> e = A () $ Lam (UName nm) (Just t) e

  e1 @@ e2 = A () $ App e1 e2
  e @:: t = A () $ Ann e t

-- helper
conv :: (a -> t -> b) -> Annotated a t -> b
conv fn (A a e) = fn a e

conv' :: (a -> c) -> (t a -> t c) -> Annotated a (t a) -> Annotated c (t c)
conv' an fn (A a e) = A (an a) (fn e)


instance Unann (Decl a) (Decl ()) where
  unann = unannD
  
unannD :: Decl a -> Decl ()
unannD = help go where
  help = conv' (const ())
  go = \case 
    FunD nm c -> FunD nm (unannE c) 
    DataD dt  -> DataD $ unann dt 
    SigD nm t -> SigD nm (unannT t)
    AliasD al -> AliasD $ unann al

instance Unann (Prog a) (Prog ()) where
  unann = unannP

unannP :: Prog a -> Prog ()
unannP (Prog ds) = Prog (map unannD ds)

-- | quantify a definition over the bound variables (or dont quantify if there are no bound)
quantify :: [(Name, Kind)] -> Type a Poly -> Type a Poly
quantify bound = if length bound > 0 then (\(A ann t) -> foldr (\(nm,k) t' -> A ann $ Forall nm k t') (A ann t) bound) else id

-- substitute type for name in expr (traverses and substitutes in annotations)
substTVarInExpr :: Type a Poly -> Name -> Expr a -> Expr a 
substTVarInExpr new nm = go where
  go (A a e') = A a $ go' e'
  go' e' = case e' of
    Var _ -> e'
    ClockVar _ -> e'
    TickVar _ -> e'
    Ann e t -> Ann e (subst new nm t)
    App e1 e2 -> App (go e1) (go e2)
    -- TODO: deal with name capture here
    Lam v mty e -> Lam v (subst new nm <$> mty) (go e)
    TickAbs v kappa e -> TickAbs v kappa (go e)
    ClockAbs kappa e -> ClockAbs kappa (go e)
    Tuple es -> Tuple (map go es)
    Let p e1 e2 -> Let p (go e1) (go e2)
    Case e clauses -> Case (go e) $ map (\(p,c) -> (p, go c)) clauses
    Prim p -> e'

-- ridiculous to copy-paste all this stuff..
substClockVarInExpr :: Expr a -> Name -> Expr a -> Expr a 
substClockVarInExpr new nm = go where
  go (A a e') = 
    case e' of
      Var _ -> A a e'
      ClockVar v
        | v == nm -> new
        | otherwise -> A a e'
      TickVar _ -> A a e'
      Ann e t -> A a $ Ann e t -- (subst new nm t)
      App e1 e2 -> A a $ App (go e1) (go e2)
      -- TODO: deal with name capture here
      Lam v mty e -> A a $ Lam v mty (go e)
      TickAbs v kappa e -> A a $ TickAbs v kappa (go e)
      ClockAbs kappa e -> A a $ ClockAbs kappa (go e)
      Tuple es -> A a $ Tuple (map go es)
      Let p e1 e2 -> A a $ Let p (go e1) (go e2)
      Case e clauses -> A a $ (Case (go e) $ map (\(p,c) -> (p, go c)) clauses)
      Prim p -> A a e'