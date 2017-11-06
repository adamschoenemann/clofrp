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
import Control.Monad.Identity

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
nat = A () . Prim . P.Integer

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

forAll' :: [(Name, Kind)] -> Type () Poly -> Type () Poly
forAll' nms t = foldr fn t $ nms where
  fn (nm,k) acc = A () $ Forall nm k acc

clocks :: [String] -> Type () Poly -> Type () Poly
clocks nms t = forAll' (map (\x -> (UName x, ClockK)) nms) t

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

lete :: Pat () -> Expr () -> Expr () -> Expr ()
lete p e1 e2 = A () $ Let p e1 e2

later :: Name -> Type () Poly -> Type () Poly
later n t = A () $ Later (A () $ TVar n) t

typeapp :: Expr () -> Type () Poly -> Expr ()
typeapp e t = A () $ TypeApp e t

tick :: Expr () 
tick = A () $ Prim P.Tick


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

traverseAnnos :: Monad m => (Type a Poly -> m (Type a Poly)) -> Expr a -> m (Expr a)
traverseAnnos fn = go where
  go (A a expr') = go' expr' where
    go' e' = case e' of
      Var _ -> pure $ A a e'
      TickVar _ -> pure $ A a e'
      Ann e t -> A a <<< Ann <$> go e <*> fn t
      App e1 e2 -> A a <<< App <$> go e1 <*> go e2
      -- TODO: deal with name capture here
      Lam v (Just ty) e -> do 
        ty' <- fn ty
        A a . Lam v (Just ty') <$> go e
      Lam v Nothing   e -> A a . Lam v Nothing <$> go e

      -- -- FIXME: Hack
      TickAbs v kappa e -> 
        fn (A a $ TVar kappa) >>= \case  
          A _ (TVar kappa') -> A a . TickAbs v kappa' <$> go e
          _                 -> error "Incorrect substitution of tick abstraction annotation"

      Tuple es -> A a . Tuple <$> (sequence $ map go es)
      Let p e1 e2 -> A a <<< Let p <$> go e1 <*> go e2
      Case e clauses -> A a <<< Case <$> go e <*> sequence (map (\(p,c) -> (p,) <$> go c) clauses)
      TypeApp e t -> A a <<< TypeApp <$> go e <*> fn t 
      Prim p -> pure $ A a e'
    (<<<) = (.) . (.)

-- substitute type for name in expr (traverses and substitutes in annotations and type applications)
substTVarInExpr :: Type a Poly -> Name -> Expr a -> Expr a 
substTVarInExpr new nm = runIdentity . traverseAnnos (Identity . subst new nm)
