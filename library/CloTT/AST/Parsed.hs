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
import Data.Char (isUpper)
import qualified CloTT.AST.Prim as P
import qualified Data.Map.Strict as M

type Type a = Annotated a (Type' a)

data Type' a
  = TFree Name
  | TApp (Type a) (Type a)
  | Type a :->: Type a
  | Forall [Name] (Type a)
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
  | Case (Expr a) [(Pat a, Expr a)]
  | Prim P.Prim
  deriving (Show, Eq, Data, Typeable)

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

forAll :: [String] -> Type () -> Type ()
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
unannT (A _ t) = A () $ unannT' t

unannT' :: Type' a -> Type' ()
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
  Case e clauses -> Case (unann e) $ map (\(p,e) -> (unannPat p, unann e)) clauses
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

-- Program "elaboration"
-- Go through a parsed program and compute the type signatures of the constructors and
-- the kinds of the data-types. Also checks that all tlds have signatures and there are
-- no orphan signatures
type Defs a = M.Map Name (Expr a)
type ElabRes a = (KiCtx, Defs a, TyCtx, TyCtx)
elabProg :: Prog a -> Result (KiCtx, TyCtx, Defs a)
elabProg (Prog decls) =
  let (kinds, funds, sigds, cnstrs) = foldr folder (M.empty, M.empty, M.empty, M.empty) decls 

      folder :: Decl a -> ElabRes a -> ElabRes a
      folder (A _ x) (ks, fs, ss, cs) = case x of
        DataD nm k b cs' -> (M.insert nm k ks, fs, ss, elabCs nm b cs' `M.union` cs)
        FunD nm e        -> (ks, M.insert nm e fs, ss, cs)
        SigD nm t        -> (ks, fs, M.insert nm (unannT t) ss, cs)

      defsNoSig = funds `M.difference` sigds
      sigsNoDef = sigds `M.difference` funds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
        
  in case () of
      _ | not defsHaveSigs -> tyErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> tyErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> pure (kinds, sigds `M.union` cnstrs, funds)

checkElabedProg :: (KiCtx, TyCtx, Defs a) -> Result ()
checkElabedProg (kinds, types, defs) = do
  checkTypes
  checkDefs
  pure ()
  where 
    checkTypes = traverse (validType kinds) types
    checkDefs  = M.traverseWithKey traverseDefs defs

      -- we have implicit recursion going on here. In the future, we should probably disallow this
    traverseDefs k expr = case M.lookup k types of
      Just ty -> check types expr ty
      Nothing -> error $ "Could not find " ++ show k ++ " in context even after elaboration. Should not happen"

checkProg :: Prog a -> Result ()
checkProg = (checkElabedProg =<<) . elabProg

-- "Elaborate" the constructors of a type, return a mapping from constructor names
-- to their types, e.g.
-- `data Maybe a = Nothing | Just a` gives
-- Nothing : Maybe a
-- Just : a -> Maybe a
elabCs :: Name -> [Name] -> [Constr a] -> M.Map Name (Type ())
elabCs tyname bound cs = M.fromList $ map fn cs where
  fullyApplied = foldl (@@:) (A () $ TFree tyname) $ map (A () . TFree) bound
  fn (A _ (Constr nm params)) = (nm, quantify $ foldr (@->:) fullyApplied $ map unannT params)
  quantify = if length bound > 0 then A () . Forall bound else id

-- declIsWellformed :: KiCtx -> Decl a -> Result ()
-- declIsWellformed ctx = \case 
--   DataD nm kind bound cs' -> (M.insert nm k ks, fs, ss, elabCs nm b cs' `M.union` cs)
--   FunD nm _e       -> (ks, M.insert nm x fs, ss, cs)
--   SigD nm t        -> (ks, fs, M.insert nm (unannT t) ss, cs)
--   where
--     boundKinds :: [Name] -> KiCtx
--     boundKinds = M.fromList . map (\nm -> (nm, Star))


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


check :: TyCtx -> Expr a -> Type () -> Result ()
check ctx annce@(A _ cexpr) (A _ annty) = check' cexpr annty where
  check' :: Expr' a -> Type' () -> Result ()
  check' expr       (Forall vs (A _ tau))  = check' expr tau 

  check' (Lam nm Nothing bd)    (ta :->: tb) = check (M.insert nm ta ctx) bd tb
  check' (Lam nm (Just ta') bd) (ta :->: tb) 
    | unannT ta' == ta = check (M.insert nm ta ctx) bd tb
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

infer :: TyCtx -> Expr a -> Result (Type ())
infer ctx (A _ e) = infer' ctx e

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
checkClauses :: TyCtx -> (Type (), Maybe (Type ())) -> [(Pat a, Expr a)] -> Result (Type ())
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
checkPat :: TyCtx -> Pat a -> Type () -> Result TyCtx
checkPat ctx (A _ pat) ty = 
  case pat of
    Bind nm -> pure $ M.insert nm ty ctx
    Match nm bound -> case M.lookup nm ctx of
      Nothing  -> tyErr $ "Pattern " ++ show nm ++ " not found in context."
      -- TODO: Check if it is actually a constructor and not just a function
      Just cty -> bind ctx nm bound cty ty

-- in a context, bind a pattern (a constructor name and a list of sub-patterns) of a type, with an expected type,
-- and extend the context with the resulting bindings.
-- TODO: We should keep a map of constructors and destructors instead of merging it into the type context
-- and then having this quite complex logic to re-capture how to bind constructors and stuf
bind :: TyCtx -> Name -> [Pat a] -> Type () -> Type () -> Result TyCtx
bind ctx nm [] (A _ cty) (A _ expected) = 
  case expected of 
    A _ t1 :->: A _ t2 -> tyErr $ "Constructor " ++ show nm ++ " requires parameters."
    Forall _ _        -> tyErr "I have no clue what to do with foralls..."
    _                 -> 
      if cty == expected
        then pure ctx 
        else tyErr $ "Cannot check " ++ show (unannT' cty) ++ " against expected type " ++ show (unannT' expected)
                  ++ " in pattern for " ++ show nm
bind ctx nm (b : bs) (A _ cty) expected =
  case cty of 
    t1 :->: t2 -> do 
      nctx <- checkPat ctx b t1
      bind nctx nm bs t2 expected

    Forall _ _ -> tyErr "I have no clue what to do with foralls..."
    _          -> tyErr $ "Cannot bind pattern " ++ show (unannPat b) ++ " to type " ++ show (unannT' cty)



inferPrim :: P.Prim -> Result (Type ())
inferPrim = \case
  P.Unit   -> pure "Unit"
  P.Bool _ -> pure "Bool"
  P.Nat _  -> pure "Nat"

