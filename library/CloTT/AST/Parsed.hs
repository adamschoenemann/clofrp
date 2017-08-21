{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module CloTT.AST.Parsed ( 
  module CloTT.AST.Parsed,
  module CloTT.AST.Name,
  P.Prim(..)
) where

import CloTT.Annotated (Annotated(..))
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
  -- |    name kind bound  constructors
  | DataD Name Kind [Name] [Constr a]
  | SigD Name (Type a)
  deriving (Show, Eq, Data, Typeable)

type Constr a = Annotated a (Constr' a)
data Constr' a
  = Constr Name [Type a]
  deriving (Show, Eq, Data, Typeable)

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

the :: Type () -> Expr () -> Expr ()
the t e = A () $ Ann e t

constr :: Name -> [Type ()] -> Constr ()
constr nm ts = A () $ Constr nm ts

datad :: Name -> Kind -> [Name] -> [Constr ()] -> Decl ()
datad nm k b cs = A () $ DataD nm k b cs

fund :: Name -> Expr () -> Decl ()
fund nm e =  A () $ FunD nm e

sigd :: Name -> Type () -> Decl ()
sigd nm t =  A () $ SigD nm t

prog :: [Decl ()] -> Prog ()
prog = Prog

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

  e1 @@ e2 = A () $ App e1 e2

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
  Prim p -> Prim p
    

unann :: Expr a -> Expr ()
unann = unannI

infix 9 ~=~
(~=~) :: Expr a -> Expr b -> Bool
e1 ~=~ e2 = unann e1 == unann e2

-- Program "elaboration"
-- Go through a parsed program and compute the type signatures of the constructors and
-- the kinds of the data-types. Also check that all tlds have signatures and there are
-- no orphan signatures
-- TODO: Determine where and how to check that data decls and type annotations are well-formed
-- Should we do it linearly? Or generate "constraints" on e.g. type kinds and solve them?
elabProg :: Prog a -> Result (KiCtx, TyCtx)
elabProg (Prog decls) =
  let (kinds, funds, sigds, cnstrs) = foldr folder (M.empty, M.empty, M.empty, M.empty) decls 

      folder (A _ x) (ks, fs, ss, cs) = case x of
        DataD nm k b cs' -> (M.insert nm k ks, fs, ss, elabCs nm b cs' `M.union` cs)
        FunD nm _e       -> (ks, M.insert nm x fs, ss, cs)
        SigD nm t        -> (ks, fs, M.insert nm (unannT t) ss, cs)

      defsNoSig = sigds `M.difference` funds
      sigsNoDef = funds `M.difference` sigds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
  in case () of
      _ | not defsHaveSigs -> tyErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> tyErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> pure (kinds, sigds `M.union` cnstrs)

elabCs :: Name -> [Name] -> [Constr a] -> M.Map Name (Type ())
elabCs tyname bound cs = M.fromList $ map fn cs where
  fullyApplied = foldl (@@:) (A () $ TFree tyname) $ map (A () . TFree) bound
  fn (A _ (Constr nm params)) = (nm, foldr (@->:) fullyApplied $ map unannT params)

-- Type checking 

type KiCtx = M.Map Name Kind
type TyCtx = M.Map Name (Type ())

empty :: TyCtx
empty = M.empty

emptyk :: KiCtx
emptyk = M.empty

ctx :: [(Name, Type ())] -> TyCtx
ctx = M.fromList

ctxk :: [(Name, Kind)] -> KiCtx
ctxk = M.fromList

type TyErr = String
type Result t = Either TyErr t

tyErr :: String -> Result a
tyErr = Left

check0 :: Expr a -> Type () -> Result ()
check0 = check empty

viewTupleT :: Type' a -> Maybe (Type' a, Type' a)
viewTupleT (A _ (A _ (TFree "Tuple") `TApp` A _ e1) `TApp` A _ e2) = Just (e1, e2)
viewTupleT _ = Nothing

kindOf :: KiCtx -> Type () -> Result Kind
kindOf ctx (A _ t) =
  case t of
    TFree v -> maybe (notFound v) pure $ M.lookup v ctx
    TApp t1 t2 -> do
      k1 <- kindOf ctx t1
      k2 <- kindOf ctx t2
      case (k1, k2) of
        (k11 :->*: k12, k2') | k11 == k2' -> pure k12
                            | otherwise -> tyErr $ "Expected " ++ show t2 ++ " to have kind " ++ show k11
        (_k1', _) -> tyErr $ "Expected " ++ show t1 ++ " to be a type constructor"
    t1 :->: t2 -> do
      k1 <- kindOf ctx t1
      k2 <- kindOf ctx t2
      case (k1, k2) of
        (Star, Star) -> pure Star
        (k1', k2')   -> tyErr $ "Both operands in arrow types must have kind *, but had " 
                    ++ show k1' ++ " and " ++ show k2' ++ " in " ++ show t
  where
    notFound v = tyErr $ "Type " ++ show v ++ " not found in context."

validType :: KiCtx -> Type () -> Result ()
validType ctx t = do
  t' <- kindOf ctx t
  if t' == Star
    then pure ()
    else tyErr $ show t ++ " is not a valid type"


check :: TyCtx -> Expr a -> Type () -> Result ()
check ctx annce@(A _ cexpr) (A _ annty) = check' cexpr annty where
  check' :: Expr' a -> Type' () -> Result ()
  check' (Lam nm Nothing bd)    (ta :->: tb) = check (M.insert nm ta ctx) bd tb
  check' (Lam nm (Just ta') bd) (ta :->: tb) 
    | unannT ta' == ta = check (M.insert nm ta ctx) bd tb
    | otherwise       = tyErr $ "parameter annotated with " ++ show (unannT ta') ++ " does not match expected " ++ show ta
  check' (Lam _ _ _) typ = tyErr $ show (unann annce) ++ " cannot check against " ++ show typ

  check' (Tuple (A _ e1) (A _ e2))  (viewTupleT -> Just (t1, t2)) = check' e1 t1 *> check' e2 t2 *> pure ()

  check' iexpr            typ               = infer' ctx iexpr =@= (A () typ)

  (=@=) :: Result (Type ()) -> Type () -> Result ()
  t1c =@= t2 = do
    t1 <- t1c
    if t1 == t2 then
      pure ()
      else tyErr (show t1 ++ " cannot check against " ++ show t2)

-- checkProg :: Prog a -> Result ()
-- checkProg prog = 
--   let (kctx, tctx) = elabProg prog

decorate :: TyErr -> Result a -> Result a
decorate err res = case res of
  Right r -> Right r
  Left err' -> Left $ err' ++ "\n" ++ err
  
infer' :: TyCtx -> Expr' a -> Result (Type ())
infer' ctx = \case
  Var nm        -> maybe (tyErr $ show nm ++ " not found in context") pure $ M.lookup nm ctx
  Ann ace aty   -> 
    let ty = unannT aty
    in  check ctx ace ty *> pure ty

  App (A _ ie) ace   -> do
    A _ r <- infer' ctx ie
    case r of
      t1 :->: t2 -> check ctx ace t1 >> pure t2
      t         -> tyErr $ show t ++ " was expected to be an arrow type"

  Lam nm (Just t1) (A _ bd) -> do
    t2 <- infer' (M.insert nm (unannT t1) ctx) bd
    pure $ unannT t1 @->: t2

  -- until we have polymorphism we cannot infer a type of forall a. a -> tau 
  Lam _nm Nothing (A _ _bd) -> 
    tyErr $ "Cannot infer type of un-annotated lambda"
  --   tryit <- decorate ("Try annotating " ++ show nm) $ infer' ctx bd
  --   pure 

  Tuple (A _ e1) (A _ e2) -> do
    t1 <- infer' ctx e1
    t2 <- infer' ctx e2
    let tuple = A () $ TFree "Tuple"
    pure $ tuple @@: t1 @@: t2

  Prim p        -> inferPrim p

inferPrim :: P.Prim -> Result (Type ())
inferPrim = \case
  P.Unit   -> pure "Unit"
  P.Bool _ -> pure "Bool"
  P.Nat _  -> pure "Nat"

