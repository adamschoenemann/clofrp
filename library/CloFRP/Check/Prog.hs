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
{-# LANGUAGE ScopedTypeVariables #-}

module CloFRP.Check.Prog where

import qualified Data.Map.Strict as M
import Debug.Trace
import Data.Data (Data, Typeable)
import Data.Monoid
import Data.Foldable
import GHC.Exts (fromList)
import Control.Monad.Reader (local)
import Control.Monad.Writer (censor)
import CloFRP.Pretty hiding ((<>))

import CloFRP.Annotated (Annotated(..))
import CloFRP.AST
import CloFRP.Check
import CloFRP.Derive

-- Program "elaboration"
-- Go through a parsed program and compute the type signatures of the constructors and
-- the kinds of the data-types. Also checks that all tlds have signatures and there are
-- no orphan signatures

-- alias for definitions
type Defs a = M.Map Name (Expr a)
type Aliases a = M.Map Name (Alias a)
type Deriving a = M.Map Name [Datatype a] -- Class to list of data-types

data ElabRes a = ElabRes
  { erKinds   :: KindCtx a    -- kinds
  , erDefs    :: Defs    a    -- function definitions
  , erSigs    :: FreeCtx a    -- signatures
  , erConstrs :: FreeCtx a    -- constructors
  , erDestrs  :: DestrCtx  a  -- destructors
  , erAliases :: Aliases a    -- type aliases
  , erDeriving :: Deriving a  -- data-types that must derive stuff
  } deriving (Show, Eq, Data, Typeable)

instance Monoid (ElabRes a) where
  mempty = ElabRes mempty mempty mempty mempty mempty mempty mempty
  er1 `mappend` er2 =
    ElabRes { erKinds    = erKinds    er1 `mappend` erKinds    er2
            , erDefs     = erDefs     er1 `mappend` erDefs     er2
            , erSigs     = erSigs     er1 `mappend` erSigs     er2
            , erConstrs  = erConstrs  er1 `mappend` erConstrs  er2
            , erDestrs   = erDestrs   er1 `mappend` erDestrs   er2
            , erAliases  = erAliases  er1 `mappend` erAliases  er2
            , erDeriving = erDeriving er1 `mappend` erDeriving er2
            }

data ElabProg a = ElabProg
  { kinds   :: KindCtx a
  , types   :: FreeCtx a
  , defs    :: Defs a
  , destrs  :: DestrCtx a
  , aliases :: Aliases a
  , instances :: InstanceCtx a
  } deriving (Show, Eq, Typeable)

{-
  type FlipSum a b = Either b a.

  foo : List (FlipSum a b) -> FlipSum (List a) b.

  expal (List (FlipSum a b))
  = expal List `TApp` expal (FlipSum a b)
  = List `TApp` (expal (FlipSum a) `TApp` expal b)
  = List `TApp` ((expal FlipSum `TApp` expal a) `TApp` expal b)
  = List `TApp` (((\y x -> Either x y) `TApp` a) `TApp` b)
  = List `TApp` (\x -> Either x a) `TApp` b
  = List `TApp` Either b a

  expal (List (Sum a b) -> Sum (List a b))
  = expal (List (Sum a b)) `TArr` expal (Sum (List a b))
  = (expal List `TApp` expal (Sum a b)) `TArr` (expal Sum `TApp` expal (List a b))
  = 
-}

-- is this just a free monad?
data AliasExpansion a
  = Done (Type a 'Poly) -- a fully expanded alias
  -- | the Name is the name of the alias
  | Ex Name (Type a 'Poly -> AliasExpansion a) -- an alias that still needs at least one application

instance Eq (AliasExpansion a) where
  Done t1 == Done t2 = t1 =%= t2
  _       == _       = False

instance Monoid a => Show (AliasExpansion a) where
  show e = showex 0 e where
    showex i (Ex _ f) = showex (i+1) (f (A mempty $ TFree (DeBruijn i)))
    showex i (Done t) = show . pretty $ t

{-
  ae (Alias FlipSum [a,b] (Either b a))
  = Ex (\x -> ae (Alias FlipSum [b] (Either b x)))
  = Ex (\x -> Ex (\y -> ae (Alias [] FlipSum (Either y x))))
  = Ex (\x -> Ex (\y -> Done (Either y x)))
-}

aliasExpansion :: a -> Alias a -> AliasExpansion a
aliasExpansion ann = go 0 . deb where 
  deb al@(Alias {alBound = b, alExpansion = ex}) =
    al { alExpansion = deBruijnify ann (map fst b) ex } 

  go i al@(Alias {alName = nm, alBound = b, alExpansion = ex}) =
    case b of
      [] -> Done ex
      _:xs -> Ex nm $ \t ->
          let ex' = subst t (DeBruijn i) ex
          in  go (i+1) (al { alBound = xs, alExpansion = ex' }) 

-- Change type-variables to use debruijn indices based on the order induced
-- by the second argument. Type-variables that do not appear in the list are
-- not changed
deBruijnify :: a -> [Name] -> Type a 'Poly -> Type a 'Poly
deBruijnify ann = go 0 where
  go _ []     ty = ty
  go i (x:xs) ty = subst (A ann $ TVar (DeBruijn i)) x $ (go (i+1) xs ty)

checkRecAliases :: forall a. Aliases a -> TypingM a ()
checkRecAliases als = sequence (M.map checkAl als) *> pure () where
  checkAl (Alias {alName, alExpansion}) = checkRecAl alName alExpansion
  checkRecAl :: Name -> Type a 'Poly -> TypingM a ()
  checkRecAl name (A _ ty') = 
    case ty' of
      TFree n 
        | n == name                  -> otherErr $ show name ++ " is recursive"
        | Just al' <- M.lookup n als -> checkRecAl name (alExpansion al')
        | otherwise                  -> pure ()

      TVar _         -> pure ()
      TExists _      -> pure ()
      TApp t1 t2     -> checkRecAl name t1 *> checkRecAl name t2
      t1 :->: t2     -> checkRecAl name t1 *> checkRecAl name t2
      Forall _n _k t -> checkRecAl name t
      RecTy  t       -> checkRecAl name t
      TTuple ts      -> traverse (checkRecAl name) ts *> pure ()
      Later _k t     -> checkRecAl name t
            


{-
  ea (FlipSum a (FlipSum b c))
  = (ea (FlipSum a), ea (FlipSum b c))
  = ((Either _ _, Done a), (ea (FlipSum b), Done c))
  = (Either _ a, ((ea FlipSum, Done b), Done c))
  = (Either _ a, ((Either 2 1, Done b), Done c))
  = (Either _ a, (Either 2 b, Done c))
  = (Either _ a, Either b c)
  = (Either (Either b c) a)
-}
expandAliases :: forall a. Aliases a -> Type a 'Poly -> TypingM a (Type a 'Poly)
expandAliases als t = 
  -- fixpoint it! for recursive alias expansion
  -- recursive type aliases will make this non-terminating, so its good
  -- that we check for those first :)
  go t >>= \case 
    Done t' | t =%= t' -> pure t'
            | otherwise -> expandAliases als t'
    Ex nm _ -> wrong nm
  where
    go :: Type a 'Poly -> TypingM a (AliasExpansion a)
    go (A ann ty') = 
      case ty' of
        TFree n 
          | Just al <- M.lookup n als -> pure $ aliasExpansion ann al
          | otherwise                 -> done (A ann $ ty')

        TVar n     -> done (A ann ty')
        TExists n  -> done (A ann ty')
        TApp t1 t2 -> 
          (go t1, go t2) &&& \case
            (Done t1', Done t2') -> done (A ann $ TApp t1' t2')
            (Done t1', Ex nm f2) -> wrong nm
            (Ex _ f1, Done t2')  -> pure $ f1 t2'
            (Ex nm f1, Ex _ f2)  -> wrong nm

        t1 :->: t2   -> 
          (go t1, go t2) &&& \case
            (Done t1', Done t2') -> done (A ann $ t1' :->: t2')
            (Ex nm _, _)         -> wrong nm
            (_, Ex nm _)         -> wrong nm

        Forall n k t1 -> 
          go t1 >>= \case
            Done t1' -> done $ A ann $ Forall n k t1'
            Ex nm _ -> wrong nm

        RecTy t1 -> 
          go t1 >>= \case
            Done t1' -> done $ A ann $ RecTy t1'
            Ex nm _ -> wrong nm
        
        TTuple ts -> do 
          ts' <- traverse fn ts
          done (A ann $ TTuple ts')
          where
            fn tt = go tt >>= \case
              Done tt' -> pure tt'
              Ex nm _ -> wrong nm
        
        Later k t1 -> 
          go t1 >>= \case
            Done t1' -> done $ A ann $ Later k t1'
            Ex nm _ -> wrong nm

    (c1, c2) &&& fn = do
      e1 <- c1
      e2 <- c2
      fn (e1, e2)

    done = pure . Done

    wrong :: Name -> TypingM a r
    wrong nm 
      | Just al <- M.lookup nm als = partialAliasApp al
      | otherwise                  = otherErr $ "alias " ++ show nm ++ " not in context. Should never happen"

collectDecls :: Prog a -> ElabRes a
collectDecls (Prog decls) = foldr folder mempty decls where
    -- TODO: Check for duplicate defs/signatures/datadecls
    folder :: Decl a -> ElabRes a -> ElabRes a
    folder (A _ x) er@(ElabRes {erKinds = ks, erConstrs = cs, erDestrs = ds, erDefs = fs, erSigs = ss, erAliases = als, erDeriving = drv}) = case x of
      DataD dt@(Datatype nm b cs' derivs) ->
        let (tys, dstrs) = elabCs nm b cs' 
            drv' = foldr (\x acc -> M.insertWith (++) (UName x) [dt] acc) drv derivs
        in  er {erKinds = extend nm (dtKind dt) ks, erConstrs = tys <> cs, erDestrs = dstrs <> ds, erDeriving = drv'}

      FunD nm e        -> er {erDefs = M.insert nm e fs}
      SigD nm t        -> er {erSigs = extend nm t ss}
      AliasD alias     -> er {erAliases = M.insert (alName alias) alias als}


elabInstances :: Applicative m => (Either String (ClassInstance a) -> m (ClassInstance a)) -> Deriving a -> m (InstanceCtx a)
elabInstances inject derivs = InstanceCtx <$> M.traverseWithKey traverseDerivs derivs where
  traverseDerivs nm dts = 
    traverse (\dt -> inject $ deriveClass nm dt) dts

-- TODO: modularize this
elabProg :: Prog a -> TypingM a (ElabProg a)
elabProg program = do
  let ElabRes kinds funds sigds cnstrs destrs aliases derivs = collectDecls program 
  let defsNoSig = funds `M.difference` unFreeCtx sigds
      sigsNoDef = unFreeCtx sigds `M.difference` funds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
  case () of
      _ | not defsHaveSigs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> do
            _ <- checkRecAliases aliases
            let FreeCtx types = sigds <> cnstrs
            expFree <- traverse (expandAliases aliases) types
            expDestrs <- DestrCtx <$> (traverse (expandDestr aliases) $ unDestrCtx destrs)
            expFunds <- traverse (traverseAnnos (expandAliases aliases)) $ funds
            instances <- elabInstances (either otherErr pure) derivs
            let allFree = FreeCtx $ expFree -- <> M.fromList derivTyps
            let allDefs = expFunds -- <> M.fromList derivDefs
            pure $ ElabProg kinds allFree allDefs expDestrs aliases instances
  where 
    -- getInstances dts = M.map mapper dts where
    --   mapper v = S.fromList $ map dtName


    expandDestr als d@(Destr {typ, args}) = do
      typ' <- expandAliases als typ
      args' <- traverse (expandAliases als) args
      pure (d {typ = typ', args = args'})

-- "Elaborate" the constructors of a type, return a mapping from constructor names
-- to their types, e.g.
-- `data Maybe a = Nothing | Just a` gives
-- Nothing : Maybe a
-- Just : a -> Maybe a
-- and a mapping from constructors to their destructors
elabCs :: forall a. Name -> [(Name,Kind)] -> [Constr a] -> (FreeCtx a, DestrCtx a)
elabCs tyname bound cs = (fromList $ map toFn cs, fromList $ map toDestr cs) where
  -- | The fully applied type e.g. Maybe a
  fullyApplied :: a -> Type a 'Poly
  fullyApplied ann = foldl' (anned ann TApp) (A ann $ TFree tyname) $ map (A ann . nameToType' . fst) bound
  -- | Convert a constructor to a function type, e.g. `Just` becomes `forall a. a -> Maybe a`
  toFn    (A ann (Constr nm args)) = (nm, quantify bound $ foldr (anned ann (:->:)) (fullyApplied ann) $ args)
  -- | Convert a constructor to a destructor, to use for pattern matches
  toDestr :: Constr a -> (Name, Destr a)
  toDestr (A ann (Constr nm args)) = 
    (nm, Destr {name = nm, typ = (fullyApplied ann), args = args, bound = bound})
  
  anned :: a -> (t -> r -> b) -> t -> r -> Annotated a b
  anned ann fn = \x y -> A ann $ fn x y

checkElabedProg :: ElabProg a -> TypingM a ()
checkElabedProg (ElabProg {kinds, types, defs, destrs, aliases, instances}) = do
  _ <- checkTypes
  _ <- checkDefs
  _ <- checkAliases
  pure ()
  where 
    checkTypes = traverse (validType kinds) (unFreeCtx types)
    checkDefs  = M.traverseWithKey traverseDefs defs
    checkAliases = traverse traverseAlias aliases

    initKinds = extend "K0" ClockK kinds
    ctx = TR {trKinds = initKinds, trFree = types, trDestrs = destrs, trCtx = mempty, trInstances = instances}
    -- we have explicit recursion allowed here. In the future, we should probably disallow this
    traverseDefs k expr = case query k types of
      Just ty -> do -- reset name state and discard old inference tree output with censor
        -- resetNameState
        -- local (const ctx) $ check expr ty
        censor (const []) $ local (const ctx) $ check expr ty
      Nothing -> error $ "Could not find " ++ show k ++ " in context even after elaboration. Should not happen"
    
    traverseAlias (Alias {alName, alBound, alExpansion}) = do
      expanded <- expandAliases aliases alExpansion
      validType kinds (quantify alBound expanded)
    


checkProg :: Prog a -> TypingM a ()
checkProg = (checkElabedProg =<<) . elabProg

runCheckProg :: TypingRead a -> Prog a -> TypingMRes a ()
runCheckProg rd p = runTypingM (checkProg p) rd initState
