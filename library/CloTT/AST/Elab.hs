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

module CloTT.AST.Elab where

import qualified Data.Map.Strict as M
import Data.Data (Data, Typeable)

import CloTT.Annotated (Annotated(..))
import CloTT.AST.Parsed

type PolyType a = Type a Poly
type PolyType' a = Type' a Poly
type MonoType a = Type a Mono
type MonoType' a = Type' a Mono

-- Program "elaboration"
-- Go through a parsed program and compute the type signatures of the constructors and
-- the kinds of the data-types. Also checks that all tlds have signatures and there are
-- no orphan signatures

type TyErr = String
type Result t = Either TyErr t

tyErr :: String -> Result a
tyErr = Left

-- These things should have better names
type KiCtx = M.Map Name Kind
type TyCtx = M.Map Name (PolyType ())

-- alias for definitions
type Defs a = M.Map Name (Expr a)
-- alias for destructors 
type Destrs = M.Map Name (Destr ())
type ElabRes a = (KiCtx, Defs a, TyCtx, TyCtx, Destrs)
data ElabProg a = ElabProg
  { kinds  :: KiCtx
  , types  :: TyCtx
  , defs   :: Defs a
  , destrs :: Destrs
  } deriving (Show, Eq, Data, Typeable)

elabProg :: Prog a -> Result (ElabProg a)
elabProg (Prog decls) =
  let (kinds, funds, sigds, cnstrs, destrs) = foldr folder (M.empty, M.empty, M.empty, M.empty, M.empty) decls 

      folder :: Decl a -> ElabRes a -> ElabRes a
      folder (A _ x) (ks, fs, ss, cs, ds) = case x of
        DataD nm k b cs' ->
          let (tys, dstrs) = elabCs nm b cs' 
          in  (M.insert nm k ks, fs, ss, tys `M.union` cs, dstrs `M.union` ds)

        FunD nm e        -> (ks, M.insert nm e fs, ss, cs, ds)
        SigD nm t        -> (ks, fs, M.insert nm (unannT t) ss, cs, ds)

      defsNoSig = funds `M.difference` sigds
      sigsNoDef = sigds `M.difference` funds
      defsHaveSigs = M.null defsNoSig -- all tlds have signatures
      sigsHaveDefs = M.null sigsNoDef -- all signatures have definitions
        
  in case () of
      _ | not defsHaveSigs -> tyErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a signature.") defsNoSig
        | not sigsHaveDefs -> tyErr $ unlines $ M.elems $ M.mapWithKey (\k _v -> show k ++ " lacks a binding.")   sigsNoDef
        | otherwise     -> pure $ ElabProg kinds (sigds `M.union` cnstrs) funds destrs

-- A destructor which is elaborated from a pattern
data Destr a = Destr
  { name   :: Name
  , typ    :: Type a Poly
  , args   :: [Type a Poly]
  } deriving (Show, Eq, Data, Typeable)

-- "Elaborate" the constructors of a type, return a mapping from constructor names
-- to their types, e.g.
-- `data Maybe a = Nothing | Just a` gives
-- Nothing : Maybe a
-- Just : a -> Maybe a
-- and a mapping from constructors to their destructors
elabCs :: Name -> [Name] -> [Constr a] -> (M.Map Name (Type () Poly), M.Map Name (Destr ()))
elabCs tyname bound cs = (M.fromList $ map toFn cs, M.fromList $ map toDestr cs) where
  -- | The fully applied type e.g. Maybe a
  fullyApplied = foldl (@@: ) (A () $ TFree tyname) $ map (A () . TFree) bound
  -- | quantify a definition over the bound variables (or dont quantify if there are no bound)
  quantify     = if length bound > 0 then (\t -> foldr (\nm t' -> A () $ Forall nm t') t bound) else id
  -- | Convert a constructor to a function type, e.g. `Just` becomes `forall a. a -> Maybe a`
  toFn    (A _ (Constr nm args)) = (nm, quantify $ foldr (@->:) fullyApplied $ map unannT args)
  -- | Convert a constructor to a destructor, to just for pattern matches
  toDestr (A _ (Constr nm args)) = 
    let ps = map unannT args
    in  (nm, Destr {name = nm, typ = quantify fullyApplied, args = ps})