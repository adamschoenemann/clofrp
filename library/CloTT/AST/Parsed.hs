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

module CloTT.AST.Parsed ( 
  module CloTT.AST.Parsed,
  module CloTT.AST.Name,
  P.Prim(..)
) where

import CloTT.Annotated (Annotated(..))
import CloTT.AST.Name
import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import Data.Char (isUpper)
import qualified CloTT.AST.Prim as P

type Type a s = Annotated a (Type' a s)

data TySort = Mono | Poly deriving (Show, Eq)

data Type' :: * -> TySort -> * where
  TFree  :: Name                      -> Type' a s
  TApp   :: Type a Poly -> Type a s    -> Type' a s
  (:->:)  :: Type a s    -> Type a s    -> Type' a s
  Forall :: [Name]      -> Type a Poly -> Type' a Poly

deriving instance Show a     => Show (Type' a s)
deriving instance Eq a       => Eq (Type' a s)
deriving instance Data a     => Data (Type' a Poly)
deriving instance Typeable a => Typeable (Type' a Poly)
  
instance IsString (Type () s) where
  fromString = A () . TFree . UName

infixl 9 @@:
(@@:) :: Type () Poly -> Type () Poly -> Type () Poly
a @@: b = A () $ a `TApp` b

infixr 2 @->:
(@->:) :: Type () s -> Type () s -> Type () s 
a @->: b = A () $ a :->: b

type Expr a = Annotated a (Expr' a)

data Expr' a
  = Var Name
  | Ann (Expr a) (Type a Poly)
  | App (Expr a) (Expr a)
  | Lam Name (Maybe (Type a Poly)) (Expr a)
  | Tuple (Expr a) (Expr a)
  | Case (Expr a) [(Pat a, Expr a)]
  | Prim P.Prim
 
deriving instance Show a     => Show (Expr' a)
deriving instance Eq a       => Eq (Expr' a)
deriving instance Data a     => Data (Expr' a)
deriving instance Typeable a => Typeable (Expr' a)

infixr 2 :->*:

type Pat a = Annotated a (Pat' a)

data Pat' a  
  = Bind Name 
  | Match Name [Pat a]
  deriving (Show, Eq, Data, Typeable)

data Kind
  = Star
  | Kind :->*: Kind
  deriving (Show, Eq, Data, Typeable)

type Decl a = Annotated a (Decl' a)
data Decl' a
  = FunD Name (Expr a)
  -- |    name kind tvars  constructors
  | DataD Name Kind [Name] [Constr a]
  | SigD Name (Type a Poly)

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

prog :: [Decl ()] -> Prog ()
prog = Prog

forAll :: [String] -> Type () Poly -> Type () Poly
forAll nm t = A () . Forall (map UName nm) $ t

caseof :: Expr () -> [(Pat (), Expr ())] -> Expr ()
caseof expr clauses = A () $ Case expr clauses

match :: Name -> [Pat ()] -> Pat ()
match nm ps = A () $ Match nm ps

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


instance IsString (Pat ()) where
  fromString nm 
    | isUpper $ head nm = error "Pat.fromString must be given a lower-chase string"
    | otherwise         = A () . Bind . UName $ nm

instance IsString (Expr ()) where
  fromString = A () . Var . UName

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

unannT :: Type a s -> Type () s
unannT (A _ t) = A () $ unannT' t

unannT' :: Type' a s -> Type' () s
unannT' = \case 
  TFree x -> TFree x
  t1 `TApp` t2 -> unannT t1 `TApp` unannT t2
  t1 :->: t2 -> unannT t1 :->: unannT t2
  Forall ts tau -> Forall ts (unannT tau)

unannD :: Decl a -> Decl ()
unannD = help go where
  help = conv' (const ())
  go = \case 
    FunD nm c -> FunD nm (unann c) 
    DataD nm k b cstrs -> DataD nm k b (map unannConstr cstrs)
    SigD nm t  -> SigD nm (unannT t)

unannP :: Prog a -> Prog ()
unannP (Prog ds) = Prog (map unannD ds)

unannConstr :: Constr a -> Constr ()
unannConstr (A _ c) =
  case c of
    Constr nm ts -> A () $ Constr nm (map unannT ts)

unannI :: Expr a -> Expr ()
unannI (A _ expr0) = A () (unannI' expr0)

unannI' :: Expr' a -> Expr' ()
unannI' = \case
  Var nm -> Var nm
  Ann e t -> Ann (unann e) (unannT t)
  App e1 e2 -> App (unannI e1) (unann e2)
  Lam nm mty e -> Lam nm (unannT <$> mty) (unannI e)
  Tuple e1 e2 -> Tuple (unann e1) (unann e2)
  Case e clauses -> Case (unann e) $ map (\(p,c) -> (unannPat p, unann c)) clauses
  Prim p -> Prim p
    
unannPat :: Pat a -> Pat ()
unannPat (A _ p) = A () $ unannPat' p

unannPat' :: Pat' a -> Pat' ()
unannPat' p = case p of
  Bind nm -> Bind nm
  Match nm ps ->  Match nm (map unannPat ps)

unann :: Expr a -> Expr ()
unann = unannI

infix 9 ~=~
(~=~) :: Expr a -> Expr b -> Bool
e1 ~=~ e2 = unann e1 == unann e2
