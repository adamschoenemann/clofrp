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

module CloTT.Check.Poly.Prog where

import qualified Data.Map.Strict as M
import Data.Data (Data, Typeable)
import Data.Monoid
import Data.Foldable
import GHC.Exts (fromList)
import Control.Monad.Reader (local)
import Debug.Trace
import CloTT.Pretty hiding ((<>))

import CloTT.Annotated (Annotated(..))
import CloTT.AST.Parsed
import CloTT.Check.Poly
import CloTT.Context

-- Program "elaboration"
-- Go through a parsed program and compute the type signatures of the constructors and
-- the kinds of the data-types. Also checks that all tlds have signatures and there are
-- no orphan signatures

-- alias for definitions
type Defs a = M.Map Name (Expr a)
type Aliases a = M.Map Name (Alias a)

type ElabRes a = 
  ( KindCtx a    -- kinds
  , Defs    a    -- function definitions
  , FreeCtx a    -- signatures
  , FreeCtx a    -- constructors
  , DestrCtx  a  -- destructors
  , Aliases a    -- type aliases
  )

data ElabProg a = ElabProg
  { kinds  :: KindCtx a
  , types  :: FreeCtx a
  , defs   :: Defs a
  , destrs :: DestrCtx a
  , aliases :: Aliases a
  } deriving (Show, Eq, Data, Typeable)

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
data ElabAlias a
  = Done (Type a Poly) -- a fully expanded alias
  -- | the Name is the name of the alias
  | Ex Name (Type a Poly -> ElabAlias a) -- an alias that still needs at least one application

instance Eq (ElabAlias a) where
  Done t1 == Done t2 = t1 =%= t2
  _       == _       = False

instance Monoid a => Show (ElabAlias a) where
  show e = showex 0 e where
    showex i (Ex _ f) = showex (i+1) (f (A mempty $ TFree (DeBruijn i)))
    showex i (Done t) = show . pretty $ t

{-
  ae (Alias FlipSum [a,b] (Either b a))
  = Ex (\x -> ae (Alias FlipSum [b] (Either b x)))
  = Ex (\x -> Ex (\y -> ae (Alias [] FlipSum (Either y x))))
  = Ex (\x -> Ex (\y -> Done (Either y x)))
-}

elabAlias :: a -> Alias a -> ElabAlias a
elabAlias ann al = go 0 (deb al) where 

  deb al@(Alias {alName, alBound, alExpansion}) =
    al { alExpansion = deBruijnify ann alBound alExpansion } 

  go i (Alias {alName, alBound, alExpansion}) =
    case alBound of
      [] -> Done alExpansion
      _:xs -> Ex alName $ \t ->
          let alExpansion' = subst t (DeBruijn i) alExpansion
          in  go (i+1) (al { alBound = xs, alExpansion = alExpansion' }) 

-- Change type-variables to use debruijn indices based on the order induced
-- by the second argument. Type-variables that do not appear in the list are
-- not changed
deBruijnify :: a -> [Name] -> Type a Poly -> Type a Poly
deBruijnify ann = go 0 where
  go i []     ty = ty
  go i (x:xs) ty = subst (A ann $ TVar (DeBruijn i)) x $ (go (i+1) xs ty)

checkRecAliases :: Aliases a -> TypingM a ()
checkRecAliases als = sequence (M.mapWithKey (\k al -> checkRecAl (alName al) (alExpansion al)) als) *> pure () where
  checkRecAl name (A _ ty') = 
    case ty' of
      TFree n 
        | n == name                  -> otherErr $ show name ++ " is recursive"
        | Just al' <- M.lookup n als -> checkRecAl name (alExpansion al')
        | otherwise                  -> pure ()

      TVar n     -> pure ()
      TExists n  -> pure ()
      TApp t1 t2 -> do
        checkRecAl name t1
        checkRecAl name t2

      t1 :->: t2   -> do
        checkRecAl name t1
        checkRecAl name t2

      Forall n t -> checkRecAl name t
            


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
expandAliases :: forall a. Aliases a -> Type a Poly -> TypingM a (Type a Poly)
expandAliases als t = 
  -- fixpoint it! for recursive alias expansion
  -- recursive type aliases will probably make this non-terminating
  go t >>= \case 
    Done t' | t =%= t' -> pure t'
            | otherwise -> expandAliases als t'
    Ex nm _ -> wrong nm
  where
    go :: Type a Poly -> TypingM a (ElabAlias a)
    go (A ann ty') = 
      case ty' of
        TFree n 
          | Just al <- M.lookup n als -> pure $ elabAlias ann al
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

        Forall n t -> 
          go t >>= \case
            Done t' -> done $ A ann $ Forall n t'
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

elabProg :: Prog a -> TypingM a (ElabProg a)
elabProg (Prog decls) = do
  (kinds, funds, sigds, cnstrs, destrs, aliases) <- foldrM folder (mempty, mempty, mempty, mempty, mempty, mempty) decls 
  let defsNoSig = funds `M.difference` (unFreeCtx sigds)
      sigsNoDef = (unFreeCtx sigds) `M.difference` funds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
  case () of
      _ | not defsHaveSigs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> do
            _ <- checkRecAliases aliases
            let FreeCtx types = sigds <> cnstrs
            expanded <- traverse (expandAliases aliases) types
            -- traceM $ show $ pretty $ M.toList expanded
            -- destrs <- DestrCtx <$> traverse ()
            pure $ ElabProg kinds (FreeCtx expanded) funds destrs aliases
  where 
    -- TODO: Check for duplicate defs/signatures/datadecls
    folder :: Decl a -> ElabRes a -> TypingM a (ElabRes a)
    folder (A _ x) (ks, fs, ss, cs, ds, als) = case x of
      DataD nm k b cs' ->
        let (tys, dstrs) = elabCs nm b cs' 
        in  pure (extend nm k ks, fs, ss, tys <> cs, dstrs <> ds, als)

      FunD nm e        -> pure (ks, M.insert nm e fs, ss, cs, ds, als)
      SigD nm t        -> pure (ks, fs, extend nm t ss, cs, ds, als)
      AliasD alias     -> pure (ks, fs, ss, cs, ds, M.insert (alName alias) alias als)



-- "Elaborate" the constructors of a type, return a mapping from constructor names
-- to their types, e.g.
-- `data Maybe a = Nothing | Just a` gives
-- Nothing : Maybe a
-- Just : a -> Maybe a
-- and a mapping from constructors to their destructors
elabCs :: forall a. Name -> [Name] -> [Constr a] -> (FreeCtx a, DestrCtx a)
elabCs tyname bound cs = (fromList $ map toFn cs, fromList $ map toDestr cs) where
  -- | The fully applied type e.g. Maybe a
  fullyApplied :: a -> Type a Poly
  fullyApplied ann = foldl (anned ann TApp) (A ann $ TFree tyname) $ map (A ann . nameToType') bound
  -- | Convert a constructor to a function type, e.g. `Just` becomes `forall a. a -> Maybe a`
  toFn    (A ann (Constr nm args)) = (nm, quantify bound $ foldr (anned ann (:->:)) (fullyApplied ann) $ args)
  -- | Convert a constructor to a destructor, to use for pattern matches
  toDestr :: Constr a -> (Name, Destr a)
  toDestr (A ann (Constr nm args)) = 
    (nm, Destr {name = nm, typ = (fullyApplied ann), args = args, bound = bound})
  
  anned :: a -> (t -> r -> b) -> t -> r -> Annotated a b
  anned ann fn = \x y -> A ann $ fn x y

checkElabedProg :: ElabProg a -> TypingM a ()
checkElabedProg (ElabProg {kinds, types, defs, destrs, aliases}) = do
  _ <- checkTypes
  _ <- checkDefs
  _ <- checkAliases
  pure ()
  where 
    checkTypes = traverse (validType kinds) (unFreeCtx types)
    checkDefs  = M.traverseWithKey traverseDefs defs
    checkAliases = traverse traverseAlias aliases

    ctx = TR {trKinds = kinds, trFree = types, trDestrs = destrs, trCtx = emptyCtx}
    -- we have explicit recursion allowed here. In the future, we should probably disallow this
    traverseDefs k expr = case query k types of
      Just ty -> {- trace ("check" ++ show k) $ -} local (const ctx) $ check expr ty
      Nothing -> error $ "Could not find " ++ show k ++ " in context even after elaboration. Should not happen"
    
    traverseAlias (Alias {alName, alBound, alExpansion}) = do
      expanded <- expandAliases aliases alExpansion
      validType kinds (quantify alBound expanded)
    


checkProg :: Prog a -> TypingM a ()
checkProg = (checkElabedProg =<<) . elabProg

runCheckProg :: TypingRead a -> Prog a -> TypingMRes a ()
runCheckProg rd prog = runTypingM (checkProg prog) rd initState