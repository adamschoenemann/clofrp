{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module CloTT.AST.Parsed ( 
  module CloTT.AST.Parsed,
  P.Prim(..)
) where

import CloTT.Annotated
import CloTT.AST.Name
import Data.String (IsString(..))
import qualified CloTT.AST.Prim as P

type Type a = Annotated a (Type' a)

data Type' a
  = TVar Name
  | Type a :->: Type a
  deriving (Show, Eq)
  
instance IsString (Type ()) where
  fromString = A () . TVar . UName

infixr 2 @->:
(@->:) :: Type () -> Type () -> Type ()
a @->: b = A () $ a :->: b

type Expr a = Annotated a (Expr' a)

data Expr' a
  = Var Name
  | Lam Name (Maybe (Type a)) (Expr a)
  | App (Expr a) (Expr a)
  | Tuple (Expr a) (Expr a)
  | Prim P.Prim
  deriving (Show, Eq)

-- Here are some combinators for creating un-annotated expressions easily
nat :: Integer -> Expr ()
nat = A () . Prim . P.Nat

true :: Expr ()
true = A () . Prim . P.Bool $ True

false :: Expr ()
false = A () . Prim . P.Bool $ False

infixr 2 @->
infixr 2 @:->
infixl 9 <|
infixl 8 @*

class IsString a => LamCalc a b | a -> b where
  (@->) :: String -> a -> a
  (@:->) :: (String, Type b) -> a -> a
  (<|) :: a -> a -> a
  (@*) :: a -> a -> a

instance IsString (Expr ()) where
  fromString = A () . Var . UName

instance LamCalc (Expr ()) () where
  nm @-> e = A () $ Lam (UName nm) Nothing e
  (nm, t) @:-> e = A () $ Lam (UName nm) (Just t) e
  e1 <| e2 = A () $ App e1 e2
  e1 @* e2 = A () $ Tuple e1 e2

unannT :: Type a -> Type ()
unannT (A _ ty) = A () (go ty) where
  go = \case
    TVar x -> TVar x
    t1 :->: t2 -> unannT t1 :->: unannT t2

unann :: Expr a -> Expr ()
unann (A _ expr) = A () (unannE expr) where
  unannE = \case
    Var nm -> Var nm
    Lam nm mty e -> Lam nm (unannT <$> mty) (unann e)
    App e1 e2 -> App (unann e1) (unann e2)
    Tuple e1 e2 -> Tuple (unann e1) (unann e2)
    Prim p -> Prim p

infix 9 ~=~
(~=~) :: Expr a -> Expr b -> Bool
e1 ~=~ e2 = unann e1 == unann e2