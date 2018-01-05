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
import Control.Monad ((<=<))
import GHC.Exts (fromList)
import Control.Monad.Reader (local)
import Control.Monad.Writer (censor, tell)
import CloFRP.Pretty hiding ((<>))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

import CloFRP.Annotated (Annotated(..))
import CloFRP.AST
import CloFRP.Check
import CloFRP.Derive

-- Program "elaboration"
-- Go through a parsed program and compute the type signatures of the constructors and
-- the kinds of the data-types. Also checks that all tlds have signatures and there are
-- no orphan signatures

-- synonym for definitions
type Defs a = M.Map Name (Expr a)
type Synonyms a = M.Map Name (Synonym a)
type Deriving a = M.Map Name [Datatype a] -- Class to list of data-types

data ElabRes a = ElabRes
  { erKinds   :: KindCtx a    -- kinds
  , erDefs    :: Defs    a    -- function definitions
  , erSigs    :: FreeCtx a    -- signatures
  , erConstrs :: FreeCtx a    -- constructors
  , erDestrs  :: DestrCtx  a  -- destructors
  , erSynonyms :: Synonyms a    -- type synonyms
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
            , erSynonyms = erSynonyms er1 `mappend` erSynonyms er2
            , erDeriving = erDeriving er1 `mappend` erDeriving er2
            }

data ElabProg a = ElabProg
  { kinds   :: KindCtx a
  , types   :: FreeCtx a
  , defs    :: Defs a
  , destrs  :: DestrCtx a
  , synonyms :: Synonyms a
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
data SynonymExpansion a
  = Done (PolyType a) -- a fully expanded synonym
  -- | the Name is the name of the synonym
  | Ex Name (PolyType a -> SynonymExpansion a) -- a synonym that still needs at least one application

instance Eq (SynonymExpansion a) where
  Done t1 == Done t2 = t1 =%= t2
  _       == _       = False

instance Monoid a => Show (SynonymExpansion a) where
  show e = showex 0 e where
    showex i (Ex _ f) = showex (i+1) (f (A mempty $ TFree (DeBruijn i)))
    showex _ (Done t) = show . pretty $ t

{-
  ae (Synonym FlipSum [a,b] (Either b a))
  = Ex (\x -> ae (Synonym FlipSum [b] (Either b x)))
  = Ex (\x -> Ex (\y -> ae (Synonym [] FlipSum (Either y x))))
  = Ex (\x -> Ex (\y -> Done (Either y x)))
-}

synonymExpansion :: a -> Synonym a -> SynonymExpansion a
synonymExpansion ann = go 0 . deb where 
  deb syn@(Synonym { synBound = b, synExpansion = ex }) =
    syn { synExpansion = deBruijnify ann (map fst b) ex } 

  go i syn@(Synonym { synName = nm, synBound = b, synExpansion = ex }) =
    case b of
      [] -> Done ex
      _:xs -> Ex nm $ \t ->
          let ex' = subst t (DeBruijn i) ex
          in  go (i+1) (syn { synBound = xs, synExpansion = ex' }) 

-- Change type-variables to use debruijn indices based on the order induced
-- by the second argument. Type-variables that do not appear in the list are
-- not changed
deBruijnify :: a -> [Name] -> PolyType a -> PolyType a
deBruijnify ann = go 0 where
  go _ []     ty = ty
  go i (x:xs) ty = subst (A ann $ TVar (DeBruijn i)) x $ (go (i+1) xs ty)

checkRecSynonyms :: forall a. Synonyms a -> TypingM a ()
checkRecSynonyms syns = sequence (M.map checkSyn syns) *> pure () where
  checkSyn (Synonym {synName, synExpansion}) = checkRecSyn synName synExpansion
  checkRecSyn :: Name -> PolyType a -> TypingM a ()
  checkRecSyn name (A _ ty') = 
    case ty' of
      TFree n 
        | n == name                  -> otherErr $ show name ++ " is recursive"
        | Just syn' <- M.lookup n syns -> checkRecSyn name (synExpansion syn')
        | otherwise                  -> pure ()

      TVar _         -> pure ()
      TExists _      -> pure ()
      TApp t1 t2     -> checkRecSyn name t1 *> checkRecSyn name t2
      t1 :->: t2     -> checkRecSyn name t1 *> checkRecSyn name t2
      Forall _n _k t -> checkRecSyn name t
      RecTy  t       -> checkRecSyn name t
      TTuple ts      -> traverse (checkRecSyn name) ts *> pure ()
      Later _k t     -> checkRecSyn name t
            


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
expandSynonyms :: forall a. Synonyms a -> PolyType a -> TypingM a (PolyType a)
expandSynonyms syns t = 
  -- fixpoint it! for recursive synonym expansion
  -- recursive type synonyms will make this non-terminating, so its good
  -- that we check for those first :)
  go t >>= \case 
    Done t' | t =%= t' -> pure t'
            | otherwise -> expandSynonyms syns t'
    Ex nm _ -> wrong nm
  where
    go :: PolyType a -> TypingM a (SynonymExpansion a)
    go (A ann ty') = 
      case ty' of
        TFree n 
          | Just syn <- M.lookup n syns -> pure $ synonymExpansion ann syn
          | otherwise                 -> done (A ann $ ty')

        TVar _     -> done (A ann ty')
        TExists _  -> done (A ann ty')
        TApp t1 t2 -> (go t1, go t2) >>*= \case
            (Done t1', Done t2') -> done (A ann $ TApp t1' t2')
            (Done _, Ex nm _)    -> wrong nm
            (Ex _ f1, Done t2')  -> pure $ f1 t2'
            (Ex nm _, Ex _ _)    -> wrong nm

        t1 :->: t2 -> (go t1, go t2) >>*= \case
            (Done t1', Done t2') -> done (A ann $ t1' :->: t2')
            (Ex nm _, _)         -> wrong nm
            (_, Ex nm _)         -> wrong nm

        Forall n k t1 -> go t1 >>= \case
            Done t1' -> done $ A ann $ Forall n k t1'
            Ex nm _ -> wrong nm

        RecTy t1 -> go t1 >>= \case
            Done t1' -> done $ A ann $ RecTy t1'
            Ex nm _ -> wrong nm
        
        TTuple ts -> done . A ann . TTuple =<< traverse fn ts where
          fn tt = go tt >>= \case
            Done tt' -> pure tt'
            Ex nm _ -> wrong nm
        
        Later k t1 -> go t1 >>= \case
            Done t1' -> done $ A ann $ Later k t1'
            Ex nm _ -> wrong nm

    (>>*=) :: Monad m => (m t1, m t2) -> ((t1, t2) -> m c) -> m c
    (c1, c2) >>*= fn = do
      e1 <- c1
      e2 <- c2
      fn (e1, e2)

    done = pure . Done

    wrong :: Name -> TypingM a r
    wrong nm 
      | Just syn <- M.lookup nm syns = partialSynonymApp syn
      | otherwise                  = otherErr $ "synonym " ++ show nm ++ " not in context. Should never happen"

collectDecls :: Prog a -> ElabRes a
collectDecls (Prog decls) = foldr folder mempty decls where
    -- TODO: Check for duplicate defs/signatures/datadecls
    folder :: Decl a -> ElabRes a -> ElabRes a
    folder (A _ x) er@(ElabRes {erKinds = ks, erConstrs = cs, erDestrs = ds, erDefs = fs, erSigs = ss, erSynonyms = syns, erDeriving = drv}) = case x of
      DataD dt@(Datatype nm _ex b cs' derivs) ->
        let (tys, dstrs) = elabCs nm b cs' 
            drv' = foldr (\x acc -> M.insertWith (++) (UName x) [dt] acc) drv derivs
        in  er {erKinds = extend nm (dtKind dt) ks, erConstrs = tys <> cs, erDestrs = dstrs <> ds, erDeriving = drv'}

      FunD nm e        -> er {erDefs = M.insert nm e fs}
      SigD nm t        -> er {erSigs = extend nm t ss}
      SynonymD synonym     -> er {erSynonyms = M.insert (synName synonym) synonym syns}


-- | Elaborate instances and expand their types with synonyms with a function
-- `inject` to go from the Either representation to a monad representation
elabInstances :: (Either String (ClassInstance a) -> TypingM a (ClassInstance a)) -> Deriving a -> TypingM a (InstanceCtx a)
elabInstances inject derivs = InstanceCtx <$> M.traverseWithKey traverseDerivs derivs where
  traverseDerivs nm dts = 
    traverse (\dt -> inject $ deriveClass nm dt) dts
  -- expandInstance ci = do 
  --   dict <- traverse tfn (ciDictionary ci)
  --   pure ci { ciDictionary = dict }
  --   where
  --     tfn (ty,expr) = do 
  --       expty <- expandSynonyms synonyms ty
  --       pure (expty, expr)

type UsageGraph = Map Name (Set Name)

usageGraph :: Defs a -> UsageGraph
usageGraph m = 
  M.mapWithKey mapping m where
    mapping k e = freeVarsExpr e

progToUseGraph :: Prog a -> UsageGraph
progToUseGraph (Prog decls) = M.fromList $ concat $ map mapping decls where
  mapping (A _ decl') = 
    case decl' of 
      FunD nm expr -> [(nm, freeVarsExpr expr)]
      DataD (Datatype {dtConstrs}) ->
         map (\(A _ (Constr nm _)) -> (nm, S.empty)) dtConstrs
      _                    -> []
  
data RoseTree a = Leaf | Node a [RoseTree a] deriving (Show, Eq)

-- takes a usage graph and a starting node and returns its dependencies
-- as a linearized list. Basically, it is just topological sort!
-- the head of the list is the given node
usageClosure :: UsageGraph -> Name -> Either (TyExcept a) [Name]
usageClosure ug nm = fst <$> visit S.empty S.empty nm where
  -- visit :: Set Name -> Set Name -> Name -> Either (TyExcept a) ([Name], Set Name)
  visit explored stack node
    | node `S.member` explored = pure ([], explored)
    | node `S.member` stack = Left (MutualRecursionErr node)
    | otherwise = do
      children <- maybe (Left $ NameNotFound node) Right $ M.lookup node ug
      (xs, e) <- recur explored (S.insert node stack) (S.toList children)
      pure (node : xs, S.insert node e)

  recur explored stack [] = pure ([], explored)
  recur explored stack (n:ns) = do
    (xs, explored') <- visit explored stack n
    (xs', explored'') <- recur explored' stack ns
    pure (xs' ++ xs, explored'')

constrsToUsageGraph :: FreeCtx a -> UsageGraph
constrsToUsageGraph (FreeCtx m) = M.map (const S.empty) m


-- TODO: modularize this
-- TODO: Check that data-types are not mutually recursive
elabProg :: Prog a -> TypingM a (ElabProg a)
elabProg program = do
  let ElabRes kinds funds sigds cnstrs destrs synonyms derivs = collectDecls program 
  let defsNoSig = funds `M.difference` unFreeCtx sigds
      sigsNoDef = unFreeCtx sigds `M.difference` funds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
  case () of
      _ | not defsHaveSigs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> do
            _ <- checkRecSynonyms synonyms
            let FreeCtx types = sigds <> cnstrs
            expFree <- traverse (expandSynonyms synonyms) types
            expDestrs <- DestrCtx <$> (traverse (expandDestr synonyms) $ unDestrCtx destrs)
            expDerivs <- traverse (expandDerivs synonyms) derivs
            expFunds <- traverse (traverseAnnos (expandSynonyms synonyms)) $ funds
            checkForMutualRecursiveDefs expFunds cnstrs
            instances <- elabInstances fromEither expDerivs
            let allFree = FreeCtx $ expFree -- <> M.fromList derivTyps
            let allDefs = expFunds -- <> M.fromList derivDefs
            pure $ ElabProg kinds allFree allDefs expDestrs synonyms instances
  where 
    expandDerivs syns ds = traverse (expandDeriv syns) ds
    expandDeriv syns d@(Datatype {dtConstrs}) = do
      constrs <- traverse expandConstr dtConstrs
      pure (d {dtConstrs = constrs})
      where
        expandConstr (A ann (Constr nm args)) = 
          A ann . Constr nm <$> traverse (expandSynonyms syns) args

    expandDestr syns d@(Destr {typ, args}) = do
      typ' <- expandSynonyms syns typ
      args' <- traverse (expandSynonyms syns) args
      pure (d {typ = typ', args = args'})
    
    checkForMutualRecursiveDefs defs constrs =
      let ug = usageGraph defs `M.union` constrsToUsageGraph constrs
      in  M.traverseWithKey (traversal ug) ug where
        traversal ug k deps = 
          either tyExcept pure (usageClosure ug k)

-- "Elaborate" the constructors of a type, return a mapping from constructor names
-- to their types, e.g.
-- `data Maybe a = Nothing | Just a` gives
-- Nothing : Maybe a
-- Just : a -> Maybe a
-- and a mapping from constructors to their destructors
elabCs :: forall a. Name -> [(Name,Kind)] -> [Constr a] -> (FreeCtx a, DestrCtx a)
elabCs tyname bound cs = (fromList $ map toFn cs, fromList $ map toDestr cs) where
  -- | The fully applied type e.g. Maybe a
  fullyApplied :: a -> PolyType a
  fullyApplied ann = foldl' (anned ann TApp) (A ann $ TFree tyname) $ map (A ann . nameToType' . fst) bound
  -- | Convert a constructor to a function type, e.g. `Just` becomes `forall a. a -> Maybe a`
  toFn    (A ann (Constr nm args)) = (nm, quantify bound $ foldr (anned ann (:->:)) (fullyApplied ann) $ args)
  -- | Convert a constructor to a destructor, to use for pattern matches
  toDestr :: Constr a -> (Name, Destr a)
  toDestr (A ann (Constr nm args)) = 
    (nm, Destr {name = nm, typ = (fullyApplied ann), args = args, bound = bound})
  
  anned :: a -> (t -> r -> b) -> t -> r -> Annotated a b
  anned ann fn = \x y -> A ann $ fn x y

-- | Check an elaborated program
-- TODO: Check derived definitions in instances
checkElabedProg :: ElabProg a -> TypingM a ()
checkElabedProg (ElabProg {kinds, types, defs, destrs, synonyms, instances}) = do
  _ <- checkTypes
  _ <- checkDefs
  _ <- checkSynonyms
  _ <- local (const ctx) checkInstances
  pure ()
  where 
    checkTypes = M.traverseWithKey traverseTypes (unFreeCtx types)
    checkDefs  = M.traverseWithKey traverseDefs defs
    checkSynonyms = traverse traverseSynonym synonyms
    checkInstances = traverse traverseInstances (unInstanceCtx instances)

    -- initKinds = extend "Int" Star $ extend "K0" ClockK kinds
    ctx = initRead `mappend `TR {trKinds = kinds, trFree = types, trDestrs = destrs, trCtx = mempty, trInstances = instances}

    traverseTypes k v = validType (trKinds ctx) v `decorateErr` (Other $ show $ "When checking" <+> pretty k)

    traverseDefs k expr = case query k types of
      Just ty -> do -- reset name state and discard old inference tree output with censor
        resetNameState
        let ctx' = ctx { trFree = delete k (trFree ctx) }
        tell [(0, "============" <+> pretty k <+> "=============")]
        local (const ctx') $ check expr ty
        -- censor (const []) $ local (const ctx') $ check expr ty
      Nothing -> error $ "Could not find " ++ show k ++ " in context even after elaboration. Should not happen"
    
    traverseSynonym (Synonym {synBound, synExpansion}) = do
      expanded <- expandSynonyms synonyms synExpansion
      validType kinds (quantify synBound expanded)
    
    traverseInstances xs = traverse checkInstance xs where
      checkInstance (ClassInstance {ciDictionary = dict, ciClassName = cnm, ciInstanceTypeName = inm}) = M.traverseWithKey (checkDict cnm inm) dict
      checkDict cnm inm k (ty, expr) = check expr ty `decorateErr` err where 
        err = Other $ showW 120 $ "Checking derived definition of" <+> pretty cnm 
            <> "." <> pretty k <+> "for" <+> pretty inm <> ":" <+> line <> pretty expr
            <> line <> "against type" <> line <> pretty ty
    


checkProg :: Prog a -> TypingM a ()
checkProg = checkElabedProg <=< elabProg

runCheckProg :: TypingRead a -> Prog a -> TypingMRes a ()
runCheckProg rd p = runTypingM (checkProg p) rd initState
