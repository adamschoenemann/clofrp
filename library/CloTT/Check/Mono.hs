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

module CloTT.Check.Mono where

import qualified Data.Map.Strict as M
import Data.Foldable (foldlM)

import CloTT.Annotated (Annotated(..))
import CloTT.AST.Parsed
import CloTT.AST.Elab

data Ctx = Ctx 
  { kinds  :: KiCtx
  , types  :: TyCtx
  , destrs :: Destrs
  } deriving (Show, Eq)

addT :: Name -> Type () -> Ctx -> Ctx
addT nm t ctx@(Ctx {types}) = ctx {types = M.insert nm t types}

addK :: Name -> Kind -> Ctx -> Ctx
addK nm t ctx@(Ctx {kinds}) = ctx {kinds = M.insert nm t kinds}

addD :: Name -> Destr () -> Ctx -> Ctx
addD nm t ctx@(Ctx {destrs}) = ctx {destrs = M.insert nm t destrs}

lookupVar :: Name -> Ctx -> Result (Type ())
lookupVar nm ctx@(Ctx {types}) = 
  maybe (tyErr $ "variable " ++ show nm ++ " not found in context") pure $ M.lookup nm types

lookupDestr :: Name -> Ctx -> Result (Destr ())
lookupDestr nm ctx@(Ctx {destrs}) = 
  maybe (tyErr $ "pattern " ++ show nm ++ " not found in context") pure $ M.lookup nm destrs

empty :: Ctx
empty = Ctx {kinds = M.empty, types = M.empty, destrs = M.empty}

emptyt :: TyCtx
emptyt = M.empty

emptyk :: KiCtx
emptyk = M.empty

tymap :: [(Name, Type ())] -> TyCtx
tymap = M.fromList

tyctx :: [(Name, Type ())] -> Ctx
tyctx xs = empty {types = M.fromList xs}

ctxk :: [(Name, Kind)] -> KiCtx
ctxk = M.fromList



check0 :: Expr a -> Type () -> Result ()
check0 = check empty

viewTupleT :: Type' a -> Maybe (Type' a, Type' a)
viewTupleT (A _ (A _ (TFree "Tuple") `TApp` A _ e1) `TApp` A _ e2) = Just (e1, e2)
viewTupleT _ = Nothing

-- Infer the kind of a type expression
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
    
    Forall vs tau -> 
      let ctx' = foldr (\v c -> M.insert v Star c) ctx vs
      in  kindOf ctx' tau
  where
    notFound v = tyErr $ "Type " ++ show v ++ " not found in context."

-- Types are only valid if they have kind *
validType :: KiCtx -> Type () -> Result ()
validType ctx t = do
  t' <- kindOf ctx t
  if t' == Star
    then pure ()
    else tyErr $ show t ++ " is not a valid type"


check :: Ctx -> Expr a -> Type () -> Result ()
check ctx annce@(A _ cexpr) (A _ annty) = check' cexpr annty where
  check' :: Expr' a -> Type' () -> Result ()
  check' expr       (Forall vs (A _ tau))  = check' expr tau 

  check' (Lam nm Nothing bd)    (ta :->: tb) = check (addT nm ta ctx) bd tb
  check' (Lam nm (Just ta') bd) (ta :->: tb) 
    | unannT ta' == ta = check (addT nm ta ctx) bd tb
    | otherwise       = tyErr $ "parameter annotated with " ++ show (unannT ta') ++ " does not match expected " ++ show ta
  check' (Lam _ _ _) typ = tyErr $ show (unann annce) ++ " cannot check against " ++ show typ

  check' (Tuple (A _ e1) (A _ e2))  (viewTupleT -> Just (t1, t2)) =
    check' e1 t1 *> check' e2 t2 *> pure ()

  check' iexpr            typ               = infer' ctx iexpr =@= (A () typ)

  (=@=) :: Result (Type ()) -> Type () -> Result ()
  t1c =@= t2 = do
    t1 <- t1c
    if t1 == t2 then
      pure ()
      else tyErr (show t1 ++ " cannot check against " ++ show t2)

decorate :: TyErr -> Result a -> Result a
decorate err res = case res of
  Right r -> Right r
  Left err' -> Left $ err' ++ "\n" ++ err

infer :: Ctx -> Expr a -> Result (Type ())
infer ctx (A _ e) = infer' ctx e

infer' :: Ctx -> Expr' a -> Result (Type ())
infer' ctx = \case
  Var nm        -> lookupVar nm ctx
  Ann ace aty   -> 
    let ty = unannT aty
    in  check ctx ace ty *> pure ty

  App (A _ ie) ace   -> do
    A _ r <- infer' ctx ie
    case r of
      t1 :->: t2 -> check ctx ace t1 >> pure t2
      t         -> tyErr $ show t ++ " was expected to be an arrow type"

  Lam nm (Just t1) (A _ bd) -> do
    t2 <- infer' (addT nm (unannT t1) ctx) bd
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

  Case (A _ e) clauses -> do
    pty <- infer' ctx e
    checkClauses ctx (pty, Nothing) clauses

  Prim p        -> inferPrim p

headResult :: TyErr -> [a] -> Result a
headResult err [] = tyErr err
headResult _ (x:_) = pure x

-- in a context, check each clause against a type of (pattern, Maybe expression)
-- if second type is nothing, it is because we do not yet know which type to infer,
-- but we should know in first recursive call
checkClauses :: Ctx -> (Type (), Maybe (Type ())) -> [(Pat a, Expr a)] -> Result (Type ())
checkClauses _ (_, mety) [] = 
  case mety of 
    Just ty -> pure ty
    Nothing -> tyErr $ "case expressions must have at least one clause"
checkClauses ctx (pty, mety) ((pat, e) : clauses) = do
  nctx <- checkPat ctx pat pty
  case mety of 
    Just ety -> check nctx e ety *> checkClauses ctx (pty, mety) clauses
    Nothing  -> do 
      ety <- infer nctx e
      checkClauses ctx (pty, Just ety) clauses

-- check that patterns type-check and return a new ctx extended with bound variables
checkPat :: Ctx -> Pat a -> Type () -> Result Ctx
checkPat ctx (A _ pat) ty = 
  case pat of
    Bind nm -> pure $ addT nm ty ctx
    Match nm pats -> case lookupDestr nm ctx of
      Left _  -> tyErr $ "Pattern " ++ show nm ++ " not found in context."
      Right destr -> checkPats ctx pats destr ty

-- in a context, check a list of patterns against a destructor and an expected type.
-- if it succeeds, it binds the names listed in the pattern match to the input context
checkPats :: Ctx -> [Pat a] -> Destr () -> Type () -> Result Ctx
checkPats ctx pats (Destr {name, typ, args}) expected
  | length pats /= length args  = tyErr $ "Expected " ++ show (length args) ++ " arguments to " ++ show name ++ " but got " ++ show (length pats)
  | typ          /= expected    = tyErr $ "Pattern '" ++ show name ++ "' has type " ++ show typ ++ " but expected " ++ show expected
  | otherwise                  = 
    foldlM folder ctx $ zip pats args
    where 
      folder acc (p, t) = checkPat acc p t

inferPrim :: Prim -> Result (Type ())
inferPrim = \case
  Unit   -> pure "Unit"
  Bool _ -> pure "Bool"
  Nat _  -> pure "Nat"

checkElabedProg :: ElabProg a -> Result ()
checkElabedProg (ElabProg {kinds, types, defs, destrs}) = do
  _ <- checkTypes
  _ <- checkDefs
  pure ()
  where 
    checkTypes = traverse (validType kinds) types
    checkDefs  = M.traverseWithKey traverseDefs defs

    ctx = Ctx {kinds = kinds, types = types, destrs = destrs}
    -- we have explicit recursion allowed here. In the future, we should probably disallow this
    traverseDefs k expr = case M.lookup k types of
      Just ty -> check ctx expr ty
      Nothing -> error $ "Could not find " ++ show k ++ " in context even after elaboration. Should not happen"

checkProg :: Prog a -> Result ()
checkProg = (checkElabedProg =<<) . elabProg