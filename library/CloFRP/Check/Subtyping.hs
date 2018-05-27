{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module CloFRP.Check.Subtyping where

import Control.Monad.Except (catchError)
import Data.Foldable (foldrM)

import CloFRP.AST.Type (PolyType, Type'(..), subst, inFreeVars)
import CloFRP.Check.TypingM ( TypingM, nameNotFound, root, branch, getKCtx
                            , getCtx, cannotSubtype, otherErr, TyExcept(..)
                            , withCtx, substCtx, decorateErr, freshName, rule
                            , occursIn 
                            )
import CloFRP.Check.Contexts ( LocalCtx, containsTVar, containsEVar, isMemberOf, (<+)
                             , CtxElem(..), dropTil, marker
                             )
import CloFRP.Annotated (Annotated(..))
import CloFRP.Check.Utils (checkWfType)
import CloFRP.Pretty
import CloFRP.Check.Instantiation (instL, instR)

isSubtypeOf :: PolyType a -> PolyType a -> TypingM a Bool
isSubtypeOf type1 type2 = 
  (subtypeOf type1 type2 >> pure True) `catchError` (const $ pure False)

-- | Under input context Γ, type A is a subtype of B, with output context ∆
-- A is a subtype of B iff A is more polymorphic than B
subtypeOf :: PolyType a -> PolyType a -> TypingM a (LocalCtx a)
subtypeOf ty1@(A ann1 typ1) ty2@(A ann2 typ2) = subtypeOf' typ1 typ2 where
  -- <:Free
  subtypeOf' (TFree x) (TFree x') = do
    kctx <- getKCtx
    case () of
      _ | not (x `isMemberOf` kctx) ->
            root ("[<:Free]") *> nameNotFound x
        | not (x' `isMemberOf` kctx) ->
            root ("[<:Free]") *> nameNotFound x'
        | x == x' ->
            root ("[<:Free]" <+> pretty ty1 <+> "<:" <+> pretty ty2) *> getCtx
        | otherwise ->
            root ("[<:Free]" <+> pretty ty1 <+> "<:" <+> pretty ty2) *> cannotSubtype ty1 ty2

  -- <:Var
  subtypeOf' (TVar x) (TVar x')
        | x == x'   = do
            ctx <- getCtx
            if ctx `containsTVar` x
              then root ("[<:Var]" <+> pretty ty1 <+> "<:" <+> pretty ty2) *> getCtx
              else root ("[<:Var]") *> otherErr ("universal variable " ++ show x ++ " not found.")
        | otherwise =
            root ("[<:Var]" <+> pretty ty1 <+> "<:" <+> pretty ty2) *> cannotSubtype ty1 ty2

  -- <:Exvar
  subtypeOf' (TExists a) (TExists a')
    | a == a' = do
      ctx <- getCtx
      root $ "[<:Exvar]" <+> pretty ty1 <+> "<:" <+> pretty ty2
      if ctx `containsEVar` a
        then pure ctx
        else branch $ nameNotFound a

  -- <:->
  subtypeOf' (a1 :->: a2) (b1 :->: b2) = do
    root $ "[<:->]" <+> pretty ty1 <+> "<:" <+> pretty ty2
    theta <- branch (b1 `subtypeOf` a1)
    a2' <- substCtx theta a2 `decorateErr` (Other "<:->.1")
    b2' <- substCtx theta b2` decorateErr` (Other "<:->.2")
    withCtx (const theta) $ branch (a2' `subtypeOf` b2')

  -- <:∀R
  subtypeOf' _t1 (Forall alpha k (A ann t2)) = do
    alpha' <- freshName
    rule "<:∀R" (pretty ty1 <+> "<:" <+> pretty ty2)
    let ty2' = subst (A ann $ TVar alpha') alpha (A ann t2)
    theta <- withCtx (\g -> g <+ Uni alpha' k) $ branch (ty1 `subtypeOf` ty2')
    pure $ dropTil (Uni alpha' k) theta

  -- <:∀L
  subtypeOf' (Forall alpha k (A at1 t1)) _ = do
    rule "<:∀L" (pretty ty1 <+> "<:" <+> pretty ty2)
    alpha' <- freshName
    let t1' = subst (A at1 $ TExists alpha') alpha (A at1 t1)
    theta <- withCtx (\g -> g <+ marker alpha' <+ Exists alpha' k) $ branch (t1' `subtypeOf` ty2)
    pure $ dropTil (Marker alpha') theta

  -- <:TApp
  subtypeOf' (TApp a1 a2) (TApp b1 b2) = do
    rule "<:TApp" (pretty ty1 <+> "<:" <+> pretty ty2)
    theta <- branch $ a1 `subtypeOf` b1
    a2' <- substCtx theta a2
    b2' <- substCtx theta b2
    branch $ withCtx (const theta) $ a2' `subtypeOf` b2'

  -- <:Rec
  subtypeOf' (RecTy b1) (RecTy b2) = do
    rule "<:Rec" (pretty ty1 <+> "<:" <+> pretty ty2)
    branch $ b1 `subtypeOf` b2

  -- <:Tuple
  subtypeOf' (TTuple ts1) (TTuple ts2) = do
    root $ "[<:Tuple]" <+> pretty ty1 <+> "<:" <+> pretty ty2
    ctx <- getCtx
    foldrM (\(t1, t2) acc -> branch $ withCtx (const acc) $ t1 `subtypeOf` t2) ctx (zip ts1 ts2)

  -- <:Later
  subtypeOf' (Later a1 a2) (Later b1 b2) = do
    root $ "[<:Later]" <+> pretty ty1 <+> "<:" <+> pretty ty2
    theta <- branch $ a1 `subtypeOf` b1
    a2' <- substCtx theta a2
    b2' <- substCtx theta b2
    branch $ withCtx (const theta) $ a2' `subtypeOf` b2'

  -- <:InstantiateL
  subtypeOf' (TExists ahat) _
    | ahat `inFreeVars` ty2 = root "[InstantiateL] OccursError!" *> occursIn ahat ty2
    | otherwise = do
        root $ "[InstantiateL]" <+> "^" <> pretty ahat <+> ":<=" <+> pretty ty2
        _ <- checkWfType (A ann1 $ TExists ahat)
        r <- branch (ahat `instL` ty2)
        pure r

  -- <:InstantiateR
  subtypeOf' _ (TExists ahat)
    | ahat `inFreeVars` ty1 = root ("[InstantiateR] OccursError in" <+> pretty ty1 <+> ">=:" <+> pretty ty2) *> occursIn ahat ty1
    | otherwise = do
        root $ "[InstantiateR]" <+> pretty ty1 <+> "=<:" <+> "^" <> pretty ahat
        _ <- checkWfType (A ann2 $ TExists ahat)
        r <- branch (ty1 `instR` ahat)
        pure r


  subtypeOf' t1 t2 = do
    -- root $ "[SubtypeError!]" <+> (fromString . show . unann $ t1) <+> "<:" <+> (fromString . show . unann $ t2)
    root $ "[SubtypeError!]" <+> pretty t1 <+> "<:" <+> pretty t2
    cannotSubtype ty1 ty2