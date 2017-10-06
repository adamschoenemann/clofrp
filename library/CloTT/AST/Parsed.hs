{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
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


infixr 2 :->*:

data Kind
  = Star
  | Kind :->*: Kind
  deriving (Show, Eq, Data, Typeable)

instance Pretty Kind where
  pretty = rndr False where
    rndr p = \case 
      Star -> "*"
      k1 :->*: k2 -> parensIf $ rndr True k1 <+> "->" <+> rndr False k2
      where
        parensIf = if p then parens else id
    


type Decl a = Annotated a (Decl' a)
data Decl' a
  = FunD Name (Expr a)
  -- |    name kind tvars  constructors
  | DataD Name Kind [Name] [Constr a]
  | SigD Name (Type a Poly)
  | AliasD (Alias a)

deriving instance Show a     => Show (Decl' a)
deriving instance Eq a       => Eq (Decl' a)
deriving instance Data a     => Data (Decl' a)
deriving instance Typeable a => Typeable (Decl' a)

type Constr a = Annotated a (Constr' a)
data Constr' a
  = Constr Name [Type a Poly]

deriving instance Show a     => Show (Constr' a)
deriving instance Eq a       => Eq (Constr' a)
deriving instance Data a     => Data (Constr' a)
deriving instance Typeable a => Typeable (Constr' a)

data Prog a = Prog [Decl a]
  deriving (Show, Eq, Data, Typeable)


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
true = A () . Prim . P.Bool $ True

false :: Expr ()
false = A () . Prim . P.Bool $ False

the :: Type () Poly -> Expr () -> Expr ()
the t e = A () $ Ann e t

constr :: Name -> [Type () Poly] -> Constr ()
constr nm ts = A () $ Constr nm ts

datad :: Name -> Kind -> [Name] -> [Constr ()] -> Decl ()
datad nm k b cs = A () $ DataD nm k b cs

fund :: Name -> Expr () -> Decl ()
fund nm e =  A () $ FunD nm e

sigd :: Name -> Type () Poly -> Decl ()
sigd nm t =  A () $ SigD nm t

aliasd :: Name -> [Name] -> Type () Poly -> Decl ()
aliasd nm bs t = A () $ AliasD (Alias nm bs t)

prog :: [Decl ()] -> Prog ()
prog = Prog

forAll :: [String] -> Type () Poly -> Type () Poly
forAll nms t = foldr fn t $ map UName nms where
  fn nm acc = A () $ Forall nm acc

exists :: Name -> Type () a
exists nm = A () $ TExists nm

caseof :: Expr () -> [(Pat (), Expr ())] -> Expr ()
caseof expr clauses = A () $ Case expr clauses

match :: Name -> [Pat ()] -> Pat ()
match nm ps = A () $ Match nm ps

debrjn :: Integer -> Type () a
debrjn = A () . TVar . DeBruijn

infixr 2 @->
infixr 2 @:->
infixl 9 @@
infixl 8 @*
infixl 3 @::

class IsString a => LamCalc a t | a -> t where
  (@->) :: String -> a -> a
  (@:->) :: (String, t) -> a -> a
  (@@) :: a -> a -> a
  (@*) :: a -> a -> a
  (@::) :: a -> t -> a


instance LamCalc (Expr ()) (Type () Poly) where
  nm @-> e = A () $ Lam (UName nm) Nothing e
  (nm, t) @:-> e = A () $ Lam (UName nm) (Just t) e

  e1 @@ e2 = A () $ App e1 e2

  e1 @* e2 = A () $ Tuple e1 e2
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
    DataD nm k b cstrs -> DataD nm k b (map unannConstr cstrs)
    SigD nm t  -> SigD nm (unannT t)
    AliasD al  -> AliasD $ unann al

instance Unann (Prog a) (Prog ()) where
  unann = unannP

unannP :: Prog a -> Prog ()
unannP (Prog ds) = Prog (map unannD ds)

instance Unann (Constr a) (Constr ()) where
  unann = unannConstr

unannConstr :: Constr a -> Constr ()
unannConstr (A _ c) =
  case c of
    Constr nm ts -> A () $ Constr nm (map unannT ts)
