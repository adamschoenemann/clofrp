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
import Data.String (fromString)
import Data.Monoid
import GHC.Exts (fromList)
import Control.Monad.Reader (local)

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

type ElabRes a = 
  ( KindCtx a  -- kinds
  , Defs    a  -- function definitions
  , FreeCtx a  -- signatures
  , FreeCtx a  -- constructors
  , DestrCtx  a  -- destructors
  )

data ElabProg a = ElabProg
  { kinds  :: KindCtx a
  , types  :: FreeCtx a
  , defs   :: Defs a
  , destrs :: DestrCtx a
  } deriving (Show, Eq, Data, Typeable)

elabProg :: Prog a -> TypingM a (ElabProg a)
elabProg (Prog decls) =
  let (kinds, funds, sigds, cnstrs, destrs) = foldr folder (mempty, mempty, mempty, mempty, mempty) decls 

      folder :: Decl a -> ElabRes a -> ElabRes a
      folder (A _ x) (ks, fs, ss, cs, ds) = case x of
        DataD nm k b cs' ->
          let (tys, dstrs) = elabCs nm b cs' 
          in  (extend nm k ks, fs, ss, tys <> cs, dstrs <> ds)

        FunD nm e        -> (ks, M.insert nm e fs, ss, cs, ds)
        SigD nm t        -> (ks, fs, extend nm t ss, cs, ds)

      defsNoSig = funds `M.difference` (unFreeCtx sigds)
      sigsNoDef = (unFreeCtx sigds) `M.difference` funds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
        
  in case () of
      _ | not defsHaveSigs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> otherErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> pure $ ElabProg kinds (sigds <> cnstrs) funds destrs


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
  -- | quantify a definition over the bound variables (or dont quantify if there are no bound)
  quantify :: Type a Poly -> Type a Poly
  quantify     = if length bound > 0 then (\(A ann t) -> foldr (\nm t' -> A ann $ Forall nm t') (A ann t) bound) else id
  -- | Convert a constructor to a function type, e.g. `Just` becomes `forall a. a -> Maybe a`
  toFn    (A ann (Constr nm args)) = (nm, quantify $ foldr (anned ann (:->:)) (fullyApplied ann) $ args)
  -- | Convert a constructor to a destructor, to just for pattern matches
  toDestr :: Constr a -> (Name, Destr a)
  toDestr (A ann (Constr nm args)) = 
    (nm, Destr {name = nm, typ = quantify (fullyApplied ann), args = args})

  anned :: a -> (t -> r -> b) -> t -> r -> Annotated a b
  anned ann fn = \x y -> A ann $ fn x y

checkElabedProg :: ElabProg a -> TypingM a ()
checkElabedProg (ElabProg {kinds, types, defs, destrs}) = do
  _ <- checkTypes
  _ <- checkDefs
  pure ()
  where 
    checkTypes = traverse (validType kinds) (unFreeCtx types)
    checkDefs  = M.traverseWithKey traverseDefs defs

    ctx = TR {trKinds = kinds, trFree = types, trDestrs = destrs, trCtx = emptyCtx}
    -- we have explicit recursion allowed here. In the future, we should probably disallow this
    traverseDefs k expr = case query k types of
      Just ty -> local (const ctx) $ check expr ty
      Nothing -> error $ "Could not find " ++ show k ++ " in context even after elaboration. Should not happen"

checkProg :: Prog a -> TypingM a ()
checkProg = (checkElabedProg =<<) . elabProg

runCheckProg :: TypingRead a -> Prog a -> TypingMRes a ()
runCheckProg rd prog = runTypingM (checkProg prog) rd initState