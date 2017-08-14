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
import Data.Data
import qualified CloTT.AST.Prim as P
import qualified Data.Map.Strict as M

type Type a = Annotated a (Type' a)

data Type' a
  = TVar Name
  | Type a :->: Type a
  deriving (Show, Eq, Data, Typeable)
  
instance IsString (Type ()) where
  fromString = A () . TVar . UName

infixr 2 @->:
(@->:) :: Type () -> Type () -> Type ()
a @->: b = A () $ a :->: b

type CExpr a = Annotated a (CExpr' a)
type IExpr a = Annotated a (IExpr' a)
type Expr a  = CExpr a

data IExpr' a
  = Var Name
  | Ann (CExpr a) (Type a)
  | App (IExpr a) (CExpr a)
  | Tuple (CExpr a) (CExpr a)
  | Prim P.Prim
  deriving (Show, Eq, Data, Typeable)

data CExpr' a
  = Inf (IExpr' a)                     -- since it is just an inclusion we do not need an extra annotation
  | Lam Name (Maybe (Type a)) (CExpr a)
  deriving (Show, Eq, Data, Typeable)

-- Here are some combinators for creating un-annotated expressions easily

var :: String -> Expr ()
var = A () . Inf . Var . UName

unit :: Expr ()
unit = A () . Inf . Prim $ P.Unit

nat :: Integer -> Expr ()
nat = A () . Inf . Prim . P.Nat

true :: Expr ()
true = A () . Inf . Prim . P.Bool $ True

false :: Expr ()
false = A () . Inf . Prim . P.Bool $ False

the :: Type () -> Expr () -> Expr ()
the t e = A () $ Inf $ Ann e t

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

instance IsString (CExpr ()) where
  fromString = A () . Inf . Var . UName

instance LamCalc (CExpr ()) (Type ()) where
  nm @-> e = A () $ Lam (UName nm) Nothing e
  (nm, t) @:-> e = A () $ Lam (UName nm) (Just t) e

  (A a (Inf e1)) @@ e2 = A () $ Inf $ App (A a e1) e2
  e1             @@ _  = error (show e1 ++ " is not inferrable in application")

  e1 @* e2 = A () $ Inf $ Tuple e1 e2
  e @:: t = A () $ Inf $ Ann e t

unannT :: Type a -> Type ()
unannT (A _ ty) = A () (go ty) where
  go = \case
    TVar x -> TVar x
    t1 :->: t2 -> unannT t1 :->: unannT t2

unannC :: CExpr a -> CExpr ()
unannC (A _ expr) = A () (unannC' expr) where
  unannC' = \case
    Inf ie -> Inf $ unannI' ie
    Lam nm mty e -> Lam nm (unannT <$> mty) (unannC e)

  unannI :: IExpr a -> IExpr ()
  unannI (A _ expr0) = A () (unannI' expr0)

  unannI' = \case
    Var nm -> Var nm
    Ann e t -> Ann (unannC e) (unannT t)
    App e1 e2 -> App (unannI e1) (unannC e2)
    Tuple e1 e2 -> Tuple (unannC e1) (unannC e2)
    Prim p -> Prim p
    

unann :: CExpr a -> CExpr ()
unann = unannC

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

checkC0 :: CExpr a -> Type () -> Result ()
checkC0 = checkC empty

checkC :: Ctx -> CExpr a -> Type () -> Result ()
checkC ctx annce@(A _ cexpr) (A _ annty) = checkC' cexpr annty where
  checkC' :: CExpr' a -> Type' () -> Result ()
  checkC' (Inf iexpr)            typ         = inferI' ctx iexpr =@= (A () typ)
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

inferI' :: Ctx -> IExpr' a -> Result (Type ())
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

  Tuple ce1 ce2 -> undefined
  Prim p        -> inferPrim p

inferPrim :: P.Prim -> Result (Type ())
inferPrim = \case
  P.Unit   -> pure "Unit"
  P.Bool _ -> pure "Bool"
  P.Nat _  -> pure "Nat"

