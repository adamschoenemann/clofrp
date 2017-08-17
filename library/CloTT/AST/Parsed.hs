{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}

module CloTT.AST.Parsed ( 
  module CloTT.AST.Parsed,
  module CloTT.AST.Name,
  P.Prim(..)
) where

import CloTT.Annotated hiding (unann)
import qualified CloTT.Annotated as A
import CloTT.AST.Name
import Data.String (IsString(..))
import Data.Data (Data, Typeable)
import qualified CloTT.AST.Prim as P
import qualified Data.Map.Strict as M

type Type a = Annotated a (Type' a)

data Type' a
  = TFree Name
  | TApp (Type a) (Type a)
  | Type a :->: Type a
  deriving (Show, Eq, Data, Typeable)
  
instance IsString (Type ()) where
  fromString = A () . TFree . UName

infixl 9 @@:
(@@:) :: Type () -> Type () -> Type ()
a @@: b = A () $ a `TApp` b

infixr 2 @->:
(@->:) :: Type () -> Type () -> Type ()
a @->: b = A () $ a :->: b

type Expr a = Annotated a (Expr' a)

data Expr' a
  = Var Name
  | Ann (Expr a) (Type a)
  | App (Expr a) (Expr a)
  | Lam Name (Maybe (Type a)) (Expr a)
  | Tuple (Expr a) (Expr a)
  | Prim P.Prim
  deriving (Show, Eq, Data, Typeable)

infixr 2 :->*:

data Kind
  = Star
  | Kind :->*: Kind
  deriving (Show, Eq, Data, Typeable)

type Decl a = Annotated a (Decl' a)
data Decl' a
  = FunD Name (Expr a)
  | DataD Name Kind [Constr a]
  | SigD Name (Type a)
  deriving (Show, Eq, Data, Typeable)

type Constr a = Annotated a (Constr' a)
data Constr' a
  = Constr Name [Type a]
  deriving (Show, Eq, Data, Typeable)

-- Here are some combinators for creating un-annotated expressions easily

var :: String -> Expr ()
var = A () . Inf . Var . UName

unit :: Expr ()
unit = A () . Inf . Prim $ P.Unit

nat :: Integer -> Expr ()
nat = A () . Prim . P.Nat

true :: Expr ()
true = A () . Prim . P.Bool $ True

false :: Expr ()
false = A () . Prim . P.Bool $ False

the :: Type () -> Expr () -> Expr ()
the t e = A () $ Ann e t

constr :: Name -> [Type ()] -> Constr ()
constr nm ts = A () $ Constr nm ts

datad :: Name -> Kind -> [Constr ()] -> Decl ()
datad nm k cs = A () $ DataD nm k cs

fund :: Name -> Expr () -> Decl ()
fund nm e =  A () $ FunD nm e

sigd :: Name -> Type () -> Decl ()
sigd nm t =  A () $ SigD nm t

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

instance IsString (Expr ()) where
  fromString = A () . Var . UName

instance LamCalc (Expr ()) (Type ()) where
  nm @-> e = A () $ Lam (UName nm) Nothing e
  (nm, t) @:-> e = A () $ Lam (UName nm) (Just t) e

  (A a e1) @@ e2 = A () $ (A a e1) e2
  e1             @@ _  = error (show e1 ++ " is not inferrable in application")

  e1 @* e2 = A () $ Tuple e1 e2
  e @:: t = A () $ Ann e t

-- helper
conv :: (a -> t -> b) -> Annotated a t -> b
conv fn (A a e) = fn a e

conv' :: (a -> c) -> (t a -> t c) -> Annotated a (t a) -> Annotated c (t c)
conv' an fn (A a e) = A (an a) (fn e)

unannT :: Type a -> Type ()
unannT = help go where
  help = conv' (const ())
  go = \case
    TFree x -> TFree x
    t1 `TApp` t2 -> help go t1 `TApp` help go t2
    t1 :->: t2 -> help go t1 :->: help go t2

unannD :: Decl a -> Decl ()
unannD = help go where
  help = conv' (const ())
  go = \case 
    FunD nm c -> FunD nm (unannC c) 
    DataD nm k cstrs -> DataD nm k (map unannConstr cstrs)
    SigD nm t  -> SigD nm (unannT t)

unannConstr :: Constr a -> Constr ()
unannConstr (A _ c) =
  case c of
    Constr nm ts -> A () $ Constr nm (map unannT ts)

unannI :: Expr a -> Expr ()
unannI (A _ expr0) = A () (unannI' expr0) where
  unannI' = \case
    Var nm -> Var nm
    Ann e t -> Ann (unannC e) (unannT t)
    App e1 e2 -> App (unannI e1) (unannC e2)
    Lam nm mty e -> Lam nm (unannT <$> mty) (unannI e)
    Tuple e1 e2 -> Tuple (unannC e1) (unannC e2)
    Prim p -> Prim p
    

unann :: Expr a -> Expr ()
unann = unannI

infix 9 ~=~
(~=~) :: Expr a -> Expr b -> Bool
e1 ~=~ e2 = unann e1 == unann e2

-- Type checking 

type Ctx = M.Map Name (Type ())

empty :: Ctx
empty = M.empty

ctx :: [(Name, Type ())] -> Ctx
ctx = M.fromList

type TyErr = String
type Result t = Either TyErr t

tyErr :: String -> Result a
tyErr = Left

checkC0 :: Expr a -> Type () -> Result ()
checkC0 = checkC empty

checkC :: Ctx -> Expr a -> Type () -> Result ()
checkC ctx annce@(A _ cexpr) (A _ annty) = checkC' cexpr annty where
  checkC' :: Expr' a -> Type' () -> Result ()
  checkC' iexpr            typ               = inferI' ctx iexpr =@= (A () typ)
  checkC' (Lam nm Nothing bd)    (ta :->: tb) = checkC (M.insert nm ta ctx) bd tb
  checkC' (Lam nm (Just ta') bd) (ta :->: tb) 
    | unannT ta' == ta = checkC (M.insert nm ta ctx) bd tb
    | otherwise       = tyErr $ "parameter annotated with " ++ show (unannT ta') ++ " does not match expected " ++ show ta

  checkC' (Lam _ _ _) typ = tyErr $ show (unannC annce) ++ " cannot check against " ++ show typ

  (=@=) :: Result (Type ()) -> Type () -> Result ()
  t1c =@= t2 = do
    t1 <- t1c
    if t1 == t2 then
      pure ()
      else tyErr (show t1 ++ " cannot check against " ++ show t2)

-- inferI :: Ctx -> Expr a -> Result (Type ())
-- inferI ctx (Ann _ expr) = inferI' ctx expr

inferI' :: Ctx -> Expr' a -> Result (Type ())
inferI' ctx = \case
  Var nm        -> maybe (tyErr $ show nm ++ " not found in context") pure $ M.lookup nm ctx
  Ann ace aty   -> 
    let ty = unannT aty
    in  checkC ctx ace ty *> pure ty

  App (A _ ie) ace   -> do
    A _ r <- inferI' ctx ie
    case r of
      t1 :->: t2 -> checkC ctx ace t1 >> pure t2
      t         -> tyErr $ show t ++ " was expected to be an arrow type"

  Tuple (A _ (Inf e1)) (A _ (Inf e2)) -> do
    t1 <- inferI' ctx e1
    t2 <- inferI' ctx e2
    let tuple = A () $ TFree "Tuple"
    pure $ tuple @@: t1 @@: t2
  
  Tuple ace1 ace2 -> tyErr $ "Tuples must have inferrable elements"

  Prim p        -> inferPrim p

inferPrim :: P.Prim -> Result (Type ())
inferPrim = \case
  P.Unit   -> pure "Unit"
  P.Bool _ -> pure "Bool"
  P.Nat _  -> pure "Nat"

