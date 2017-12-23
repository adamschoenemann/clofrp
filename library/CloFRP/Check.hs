{-|
Module      : CloFRP.Check
Description : Type-checking and inference algorithm for CloFRP.

Based on Complete and Easy Bidirectional Typechecking for Higher-Rank 'Polymorphism by Joshua Dunfeld
and Neel Krishnaswami
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ImplicitParams #-}

module CloFRP.Check
  ( module CloFRP.Check
  , module CloFRP.Check.Destr
  , module CloFRP.Check.Contexts
  , module CloFRP.Check.TypingM
  )
  where

import Data.Foldable (foldlM, foldrM)
import Control.Applicative ((<|>))
import Control.Monad.Except (catchError, throwError)
import Data.Text.Prettyprint.Doc
import Data.List (find, genericLength)
import Data.Maybe (isJust)

import CloFRP.AST.Name
import qualified CloFRP.AST.Helpers as H
import CloFRP.Context
import CloFRP.Annotated
import CloFRP.AST hiding (exists)
import CloFRP.Pretty
import CloFRP.Check.Destr
import CloFRP.Check.Contexts
import CloFRP.Check.TypingM


-- | For testing
runSubtypeOf0 :: Type a 'Poly -> Type a 'Poly -> TypingMRes a (LocalCtx a)
runSubtypeOf0 t1 t2 = runSubtypeOf initRead t1 t2

-- | For testing
runSubtypeOf :: TypingRead a -> Type a 'Poly -> Type a 'Poly -> TypingMRes a (LocalCtx a)
runSubtypeOf rd t1 t2 = runTypingM (t1 `subtypeOf` t2) rd initState

-- | Run a type-checking computation in an empty context
runCheck0 :: Expr a -> Type a 'Poly -> TypingMRes a (LocalCtx a)
runCheck0 e t = runCheck initRead e t

-- | Run a type-checking computation in a given context
runCheck :: TypingRead a -> Expr a -> Type a 'Poly -> TypingMRes a (LocalCtx a)
runCheck rd e t = runTypingM (check e t) rd initState

-- | Run a type-synthesizing computation in a given context
runSynth :: TypingRead a -> Expr a -> TypingMRes a (Type a 'Poly, LocalCtx a)
runSynth rd e = runTypingM (synthesize e) rd initState

-- | Substitute a type using a context. As defined in the paper Θ[τ]. Will substitute
-- | zero or more existential type variables for something "more-solved"
substCtx :: LocalCtx a -> Type a 'Poly -> TypingM a (Type a 'Poly)
substCtx ctx (A a ty) =
  case ty of
    TFree x -> pure $ A a $ TFree x
    TVar x  -> pure $ A a $ TVar  x
    TExists x ->
      case findAssigned x ctx of
        Just tau -> substCtx ctx (asPolytype tau) -- do it again to make substitutions simultaneous (transitive)
        Nothing
          | ctx `containsEVar` x -> pure $ A a $ TExists x
          | otherwise            -> otherErr $ show $ "existential" <+> pretty x <+> "not in context"

    t1 `TApp` t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure $ A a $ t1' `TApp` t2'

    t1 :->: t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure $ A a $ t1' :->: t2'

    Forall x k t -> do
      t' <- substCtx ctx t
      pure $ A a $ Forall x k t'

    RecTy t -> do
      t' <- substCtx ctx t
      pure $ A a $ RecTy t'

    TTuple ts -> do
      A a . TTuple <$> sequence (map (substCtx ctx) ts)

    Later t1 t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure (A a $ Later t1' t2')

  `decorateErr` (Other $ show $ "During substitution of" <+> pretty (A a ty))

-- | Apply a context to itself, substituting away all solved existentials.
-- Only used for debugging to make large contexts easier to reason about.
selfapp :: LocalCtx a -> TypingM a (LocalCtx a)
selfapp (LocalCtx []) = pure $ mempty
selfapp ctx@(LocalCtx ((ahat := ty) : xs)) = do
  tys <- asMonotypeTM =<< substCtx ctx (asPolytype ty)
  LocalCtx xs' <- selfapp (LocalCtx xs)
  pure (LocalCtx $ (ahat := tys) : xs')
selfapp (LocalCtx (x : xs)) = do
  LocalCtx xs' <- selfapp (LocalCtx xs)
  pure $ LocalCtx (x : xs')

-- | Checks that a context is κ-stable - that is, the context contains no
-- lambda-bound names that mention κ in their type
mustBeStableUnder :: LocalCtx a -> Name -> TypingM a ()
mustBeStableUnder (LocalCtx xs) k = traverse traversal xs *> pure () where
  traversal ce = case ce of
    (LamB, nm) `HasType` ty
      | k `inFreeVars` ty -> otherErr $ show $ "Context not stable wrt" <+> pretty k <+> "due to" <+> pretty ce
    _                     -> pure ()

-- | Split a context at an element, yield the context before the element,
-- the element itself, and the context after the element
splitCtx :: CtxElem a -> LocalCtx a -> TypingM a (LocalCtx a, CtxElem a, LocalCtx a)
splitCtx el ctx =
  case splitCtx' el ctx of
    Nothing -> root "splitCtx" *> cannotSplit el ctx
    Just x  -> pure x

-- | Check if a context element occurs before another
-- context element in the current context
before :: CtxElem a -> CtxElem a -> TypingM a Bool
before alpha beta = before' alpha beta <$> getCtx

-- | Query the kind of a name in the current context
queryKind :: Name -> TypingM a Kind
queryKind nm = do
  ctx <- getCtx
  case ctxFind p ctx of
    Just (Exists _ k) -> pure k
    Just (Uni _ k)    -> pure k
    Just (_ := ty)    -> kindOf (asPolytype ty) `decorateErr` Other ("queryKind")
    _                 -> otherErr $ showW 3000 $ "queryKind: Cannot lookup kind of" <+> pretty nm <+> "in" <+> pretty ctx
  where
      p (Uni x _)    = x == nm
      p (Exists x _) = x == nm
      p (x := _)     = x == nm
      p _             = False

-- | Insert another context (a list of ctx-elems) into the current context at a specific element.
-- It will replace the element with the new inserted context
insertAt :: CtxElem a -> LocalCtx a -> TypingM a (LocalCtx a)
insertAt at insertee = do
  ctx <- getCtx
  case insertAt' at insertee ctx of
    Nothing   -> otherErr $ show $ "Cannot insert" <+> pretty insertee <+> "into context" <+> pretty ctx <+> "at" <+> pretty at
    Just ctx' -> pure ctx'

-- Infer the kind of a type variable from how it is used in a type
-- Its not gonna work, I think though... Instead, "spine-ify" first and
-- then filter
-- inferVarKind :: KindCtx a -> Name -> Type a 'Poly -> Either String Kind
-- inferVarKind kctx nm (A _ ty) =
--   case ty of
--     TFree v -> noInfo
--     TVar  v -> pure Star
--     TExists v -> noInfo

--     TApp (A _ (TVar v)) t2
--       | v == nm   -> do
--         k <- kindOf' kctx t2
--         pure $ k :->*: Star
--       | otherwise -> inferVarKind kctx nm t2

--     TApp t1 t2 ->
--       case inferVarKind kctx nm t1 of
--         Left _ -> inferVarKind kctx nm t2
--         Right k -> case inferVarKind kctx nm t2 of
--           Left _ -> pure k
--           Right k' -> if k == k' then pure k else Left ("Conflicting kinds inferred for" ++ show nm)

--     t1 :->: t2 ->
--       case inferVarKind kctx nm t1 of
--         Left _ -> inferVarKind kctx nm t2
--         Right k -> case inferVarKind kctx nm t2 of
--           Left _ -> pure k
--           Right k' -> if k == k' then pure k else Left ("Conflicting kinds inferred for" ++ show nm)

--     Forall v tau -> inferVarKind kctx nm tau
--   where
--     noInfo = Left $ "Cannot infer kind of type-variable " ++ show nm


-- | Get the kind of a type in the current context
kindOf :: Type a 'Poly -> TypingM a Kind
kindOf ty = go ty `decorateErr` decorate where
  go (A _ t) = do
    kctx <- getKCtx
    ctx <- getCtx
    case t of
      TFree "K0" -> pure ClockK -- FIXME: K0 Hack
      TFree v -> maybe (freeNotFound v) pure $ query v kctx

      TVar v -> queryKind v

      TExists  v -> queryKind v

      TApp t1 t2 -> do
        k1 <- go t1
        k2 <- go t2
        case (k1, k2) of
          (k11 :->*: k12, k2')
            | k11 == k2' -> pure k12
            | otherwise  ->
                otherErr $ "Expected " ++ pps t2 ++ " to have kind " ++ pps k11
          (_k1', _) -> otherErr $ "Expected " ++ pps t1 ++ " to be a type constructor"

      t1 :->: t2 -> do
        k1 <- go t1
        k2 <- go t2
        case (k1, k2) of
          (Star, Star) -> pure Star
          (k1', k2')   -> otherErr $ "Both operands in arrow types must have kind *, but had "
                      ++ pps k1' ++ " and " ++ pps k2' ++ " in " ++ pps t

      Forall v k tau -> do
        errIf (isInContext (Uni v k) <$> getCtx) (/= False) (\v' -> Other $ show $ pretty v' <+> "is already universally quantified")
        withCtx (\g -> g <+ Uni v k) $ go tau

      RecTy tau -> do
        k <- go tau
        case k of
          Star :->*: k -> pure k
          _            -> otherErr $ show $ pretty tau <+> "must have kind * -> k to be an argument to Fix"

      TTuple ts -> (traverse fn ts) *> pure Star where
        fn tt = kindOf tt >>= \case
          Star -> pure ()
          k    -> otherErr $ show $ pretty tt <+> "must have kind * but had kind" <+> pretty k

      Later k tau -> do
        k' <- go tau
        case k' of
          Star -> pure Star
          _    -> otherErr $ show $ pretty tau <+> "must have kind * at" <+> pretty ty <+> "but had kind" <+> pretty k'

    where
      freeNotFound v = do
        kctx <- getKCtx
        nameNotFound v `decorateErr` (Other $ show $ "looking up a free variable in kind-ctx" <+> pretty kctx)

  decorate = Other $ show $ "kindOf" <+> (pretty ty)

-- | Check that a type is well-formed.
checkWfType :: Type a 'Poly -> TypingM a ()
checkWfType ty = kindOf ty *> pure ()

-- | Check if a given context is well-formed
-- TODO: Also fail ctx such as [a := tau, a] or [a, a := tau]
wfContext :: forall a. LocalCtx a -> TypingM a ()
wfContext (LocalCtx elems) = (foldrM fn [] elems *> pure ())  where
  fn :: CtxElem a -> [CtxElem a] -> TypingM a [CtxElem a]
  fn el acc = do
    _ <- withCtx (const $ LocalCtx acc) $ checkIt el
    pure (el : acc)

  elem' f xs = isJust $ find (\x -> f (unann x)) xs

  -- this one refers to ctx through getCtx
  checkIt el = case el of
    Uni nm _        -> notInDom nm el
    Exists nm _     -> notInDom nm el
    (_, nm) `HasType` ty -> notInDom nm el *> checkWfType (asPolytype ty) `decorateErr` (NotWfContext el)
    nm := ty        -> notInDom nm el *> checkWfType (asPolytype ty) `decorateErr` (NotWfContext el)
    Marker nm       -> do
      _ <- notInDom nm el
      LocalCtx ctx <- getCtx
      if ((\x -> Marker nm == x) `elem'` ctx)
        then notWfContext (Marker nm)
        else pure ()

  -- TODO: fix this to account for HasType constructor as well
  notInDom nm el = do
    ctx <- getCtx
    if (isJust $ ctxFind p ctx)
      then notWfContext el
      else pure ()
    where
      p (Uni x _)    = x == nm
      p (Exists x _) = x == nm
      p (x := _)     = x == nm
      p _            = False

-- | Check if a type has kind * in a context
validType :: KindCtx a -> Type a 'Poly -> TypingM a ()
validType kctx t = do
  k <- withKCtx (const kctx) $ kindOf t
  case k of
    Star -> pure ()
    _    -> otherErr $ show $ pretty t <+> "has kind" <+> pretty k
        <+> "but expected *"

-- | Assign an unsolved variable to a type in a context
-- TODO: Optimize
assign :: Name -> Type a 'Mono -> TypingM a (LocalCtx a)
assign nm ty = do
  ctx@(LocalCtx xs) <- getCtx
  case findAssigned nm ctx of
    Just ty'
      | ty =%= ty' -> pure ctx
      | otherwise  -> otherErr $ show $ pretty nm
                  <+> "is already assigned to" <+> pretty ty'
    Nothing ->
      case foldr fn ([], False) xs of
        (xs', True) -> do
          let asserr = Other $ show $ "Assigning" <+> pretty nm <+> "to"
                    <+> pretty ty
          _ <- wfContext (LocalCtx xs') `decorateErr` asserr
          pure (LocalCtx xs')
        (xs', False) -> otherErr $ show $ pretty nm <+> ":=" <+> pretty ty <+> "Didn't assign anything"
      where
        -- TODO: Check that kindOf ty == k
        fn (Exists nm' k) (xs', _) | nm == nm' = (nm := ty : xs', True)
        fn x (xs', b)                          = (x : xs', b)

-- | Attempt to convert a type to a monotype and lift it to the TypingM monad
asMonotypeTM :: Type a s -> TypingM a (Type a 'Mono)
asMonotypeTM t = maybe (otherErr $ show $ pretty t <+> "is not a monotype") pure . asMonotype $ t

-- | Lookup a type in a given context (lifted to TypingM monad)
lookupTyTM :: Name -> LocalCtx a -> TypingM a (Type a 'Poly)
lookupTyTM nm c =
  case lookupTy nm c of
    Just t -> pure t
    Nothing -> nameNotFound nm

-- | Log that a rule of some name with some info was triggered
rule :: Doc () -> Doc () -> TypingM a ()
rule name info = do
  ctx <- selfapp =<< getCtx
  root $ sep [brackets name <+> info, indent 4 (nest 3 ("in" <+> pretty ctx))]

-- | Assert that a type is functorial, namely that there is an instance of Functor for that type
assertFunctor :: Type a 'Poly -> TypingM a ()
assertFunctor ty = findInstanceOf "Functor" ty >>= \case
  Just _ -> pure ()
  Nothing -> otherErr $ show $ "Cannot resolve functor instance of" <+> pretty ty

solve :: Name -> Type a s -> TypingM a (LocalCtx a)
solve ahat ty = do
  mty <- asMonotypeTM ty
  assign ahat mty

-- TODO: Find a way to abstract all these near-identical definitions out. Also, combine instL and instR, or
-- at least implement them both in terms of a more general combinator

-- Under input context Γ, instantiate α^ such that α^ <: A, with output context ∆
instL :: Name -> Type a 'Poly -> TypingM a (LocalCtx a)
-- InstLSolve
instL ahat ty@(A a ty') =
  (solve ahat ty <* rule "InstLSolve" (pretty ahat <+> ":<=" <+> pretty ty)) `catchError` \err ->
      case ty' of
        -- InstLReach
        TExists bhat -> do
          ak <- queryKind ahat
          bk <- queryKind bhat
          rule "InstLReach" ("^" <> pretty bhat <+> "=" <+> "^" <> pretty ahat)
          Exists ahat ak `before` Exists bhat bk >>= \case
            True -> assign bhat (A a $ TExists ahat)
            False -> otherErr $ "[InstLReach] error"

        -- InstLArr
        t1 :->: t2 -> do
          rule "InstLArr" (pretty ahat <+> ":<=" <+> pretty ty)
          af1 <- freshName
          af2 <- freshName
          let ahat1 = Exists af1 Star
          let ahat2 = Exists af2 Star
          let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
          ctx' <- insertAt (Exists ahat Star) [ahat1, ahat2, ahat := arr]
          omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
          substed <- substCtx omega t2
          withCtx (const omega) $ branch (af2 `instL` substed)

        -- InstLAllR
        Forall beta k bty -> do
          rule "InstLAllR" (pretty ahat <+> ":<=" <+> pretty ty)
          beta' <- freshName
          let bty' = subst (A a $ TVar beta') beta bty
          theta <- withCtx (\g -> g <+ Uni beta' k) $ branch (ahat `instL` bty')
          pure $ dropTil (Uni beta' k) theta

        -- InstLTApp. Identical to InstLArr
        TApp t1 t2 -> do
          rule "InstLTApp" (pretty ahat <+> ":<=" <+> pretty ty)
          af1 <- freshName
          af2 <- freshName
          t1k <- kindOf t1
          t2k <- kindOf t2
          tyk <- kindOf ty
          let expectKind = t2k :->*: tyk
          errIf (pure t1k) (/= expectKind) (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected" <+> pretty expectKind)
          let ahat1 = Exists af1 t1k
          let ahat2 = Exists af2 t2k
          let app = A a $ (A a $ TExists af1) `TApp` (A a $ TExists af2)
          ctx' <- insertAt (Exists ahat tyk) [ahat1, ahat2, ahat := app]
          omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
          substed <- substCtx omega t2
          withCtx (const omega) $ branch (af2 `instL` substed)

        -- InstLTuple
        TTuple ts -> do
          rule "InstLTuple" (pretty ty <+> "=<:" <+> pretty ahat)
          nms <- traverse (const freshName) ts
          tyk <- kindOf ty
          let existstup = A a $ TTuple $ map (A a . TExists) nms
          ctx' <- insertAt (Exists ahat tyk) (foldr (\x g -> g <+ Exists x Star) mempty nms <+ ahat := existstup)
          foldrM folder ctx' $ zip nms ts
          where
            folder (af, t) acc = do
              tsubst <- substCtx acc t
              branch $ withCtx (const acc) $ tsubst `instR` af

        -- InstLLater. Similar to instantiation of other type-combinators
        Later t1 t2 -> do
          rule "InstLLater" (pretty ahat <+> ":<=" <+> pretty ty)
          af1 <- freshName
          af2 <- freshName
          errIf (kindOf t1) (/= ClockK) (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected Clock")
          errIf (kindOf t2) (/= Star)   (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected *")
          let ahat1 = Exists af1 ClockK
          let ahat2 = Exists af2 Star
          let ltr = A a $ Later (A a $ TExists af1) (A a $ TExists af2)
          ctx' <- insertAt (Exists ahat Star) (mempty <+ ahat1 <+ ahat2 <+ ahat := ltr)
          omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
          substed <- substCtx omega t2
          r <- withCtx (const omega) $ branch (af2 `instL` substed)
          pure r

        -- InstLRec
        RecTy t -> do
          rule "InstLRec" (pretty ahat <+> ":<=" <+> pretty ty)
          a1 <- freshName
          let rt = A a $ RecTy (A a $ TExists a1)
          k <- kindOf t
          ctx' <- insertAt (Exists ahat Star) (mempty <+ Exists a1 k <+ ahat := rt)
          withCtx (const ctx') $ branch (a1 `instL` t)

        _ -> do
          rule "InstLError" ("^" <> pretty ahat <+> "=" <+> pretty ty)
          throwError err




instR :: Type a 'Poly -> Name -> TypingM a (LocalCtx a)
-- InstRSolve
instR ty@(A a ty') ahat =
  (solve ahat ty <* rule "InstRSolve" (pretty ty <+> "=<:" <+> pretty ahat)) `catchError` \err ->
        case ty' of
          -- InstRReach
          TExists bhat -> do
            ak <- queryKind ahat
            bk <- queryKind bhat
            rule "InstRReach" ("^" <> pretty ahat <+> "=" <+> "^" <> pretty bhat)
            Exists ahat ak `before` Exists bhat bk >>= \case
              True -> assign bhat (A a $ TExists ahat)
              False -> otherErr $ "[InstRReachError]"

          -- InstRArr
          t1 :->: t2 -> do
            rule "InstRArr" (pretty ty <+> "=<:" <+> pretty ahat)
            af1 <- freshName
            af2 <- freshName
            let ahat1 = Exists af1 Star
            let ahat2 = Exists af2 Star
            let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
            ctx' <- insertAt (Exists ahat Star) (mempty <+ ahat1 <+ ahat2 <+ ahat := arr)
            omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          -- InstRAllL
          Forall beta k bty -> do
            rule "InstRAllL" (pretty ty <+> "=<:" <+> pretty ahat)
            beta' <- freshName
            let bty' = subst (A a $ TExists beta') beta bty
            ctx' <- withCtx (\g -> g <+ marker beta' <+ Exists beta' k) $ branch (bty' `instR` ahat)
            (delta, _, _delta') <- splitCtx (Marker beta') ctx'
            pure delta

          -- InstRTApp. Identical to InstRArr
          TApp t1 t2 -> do
            rule "InstRTApp" (pretty ty <+> "=<:" <+> pretty ahat)
            af1 <- freshName
            af2 <- freshName
            t1k <- kindOf t1
            t2k <- kindOf t2
            tyk  <- kindOf ty
            let ahat1 = Exists af1 t1k
            let ahat2 = Exists af2 t2k
            let app = A a $ (A a $ TExists af1) `TApp` (A a $ TExists af2)
            ctx' <- insertAt (Exists ahat tyk) (mempty <+ ahat1 <+ ahat2 <+ ahat := app)
            omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          -- InstRRec
          RecTy t -> do
            rule "InstRRec" (pretty ty <+> "=<:" <+> pretty ahat)
            a1 <- freshName
            let rt = A a $ RecTy (A a $ TExists a1)
            k <- kindOf t
            ctx' <- insertAt (Exists ahat Star) (mempty <+ Exists a1 k <+ ahat := rt)
            withCtx (const ctx') $ branch (t `instR` a1)

          -- InstRTuple
          TTuple ts -> do
            rule "InstRTuple" (pretty ty <+> "=<:" <+> pretty ahat)
            nms <- traverse (const freshName) ts
            tyk <- kindOf ty
            let existstup = A a $ TTuple $ map (A a . TExists) nms
            ctx' <- insertAt (Exists ahat tyk) (foldr (\x g -> g <+ Exists x Star) mempty nms <+ ahat := existstup)
            foldrM folder ctx' $ zip nms ts
            where
              folder (af, t) acc = do
                tsubst <- substCtx acc t
                branch $ withCtx (const acc) $ af `instL` tsubst

          -- InstRLater. Similar to instantiation of other type-combinators
          Later t1 t2 -> do
            rule "InstRLater" (pretty ty <+> "=<:" <+> pretty ahat)
            af1 <- freshName
            af2 <- freshName
            errIf (kindOf t1) (/= ClockK) (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected Clock")
            errIf (kindOf t2) (/= Star)   (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected *")
            let ahat1 = Exists af1 ClockK
            let ahat2 = Exists af2 Star
            let ltr = A a $ Later (A a $ TExists af1) (A a $ TExists af2)
            ctx' <- insertAt (Exists ahat Star) (mempty <+ ahat1 <+ ahat2 <+ ahat := ltr)
            omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          _ -> do
            rule "InstRError" ("^" <> pretty ahat <+> "=" <+> pretty ty)
            throwError err
            -- otherErr $ showW 80 $ "[instR] Cannot instantiate" <+> pretty ahat <+> "to" <+> pretty ty <+> ". Cause:" <+> fromString err

-- Under input context Γ, type A is a subtype of B, with output context ∆
-- A is a subtype of B iff A is more polymorphic than B
subtypeOf :: Type a 'Poly -> Type a 'Poly -> TypingM a (LocalCtx a)
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

check :: Expr a -> Type a 'Poly -> TypingM a (LocalCtx a)
check e@(A eann e') ty@(A tann ty') = sanityCheck ty *> check' e' ty' where

  -- 1I
  check' (Prim Unit) (TFree "Unit") = getCtx
  check' (Prim (Integer _)) (TFree "Int") = getCtx
  -- PrimI
  -- check' (Prim p) _ = do
  --   (pty, theta) <- inferPrim eann p
  --   root $ "[PrimI]" <+> pretty e <+> "<=" <+> pretty ty
  --   withCtx (const theta) $ branch $ pty `subtypeOf` ty

  -- ∀I
  check' _ (Forall alpha k aty) = do
    rule "∀I" (pretty e <+> "<=" <+> pretty ty)
    alpha' <- freshName
    let alphat = A tann $ TVar alpha'
    let aty' = subst alphat alpha aty
    let esubst = substTVarInExpr alphat alpha e -- not performant but fine for now and probably not bottleneck
    (delta, _, _) <- splitCtx (Uni alpha' k) =<< withCtx (\g -> g <+ Uni alpha' k) (branch $ check esubst aty')
    pure delta

  -- ->I
  check' (Lam x mty e2) (aty :->: bty) = do
    rule "->I" (pretty e <+> "<=" <+> pretty ty)
    ctx' <- maybe getCtx (aty `subtypeOf`) mty
    let c = (LamB, x) `HasType` aty
    (delta, _, _) <- splitCtx c =<< withCtx (const $ ctx' <+ c) (branch $ check e2 bty)
    pure delta

  -- Case<=
  -- TODO: move all the marker insertion logic into checkCaseClauses instead
  check' (Case on clauses) _ = do
    root $ "[Case<=]" <+> pretty e <+> "<=" <+> pretty ty
    (pty, delta) <- branch $ synthesize on
    pty' <- substCtx delta pty
    (pty'', delta') <- withCtx (const delta) $ branch $ intros pty'
    tysubst <- substCtx delta' ty
    markerName <- freshName
    delta'' <- withCtx (const $ delta' <+ Marker markerName) $ branch $ checkCaseClauses markerName pty'' clauses tysubst
    pure delta''

  -- TickAbsI
  check' (TickAbs af k e2) (Later k' t2) = do
    rule "TickAbsI" (pretty e <+> "<=" <+> pretty ty)
    let kty = nameToType eann k
    delta <- branch $ k' `subtypeOf` kty
    kty' <- substCtx delta kty
    let c = (LamB, af) `HasType` kty'
    (theta, _, _) <- splitCtx c =<< withCtx (\g -> g <+ c) (branch $ check e2 t2)
    pure theta

  -- -- FoldApp (optimization)
  -- check' (A fann (Prim Fold) `App` e2) (RecTy fty) = do
  --   root $ "[FoldApp]" <+> pretty e <+> "<=" <+> pretty ty
  --   branch $ check e2 (A tann $ fty `TApp` ty)

  -- -- UnfoldApp (optimization)
  -- check' (A ufann (Prim Unfold) `App` e2) (ftor `TApp` unfty) = do
  --   root "[UnfoldApp]"
    -- branch $ check e2 $ unfty

  -- Tuple<=
  check' (Tuple es) (TTuple ts) = do
    root $ "[Tuple<=]" <+> pretty e <+> "<=" <+> pretty ty
    ctx <- getCtx
    -- TODO: How should we propagate contexts here? right-to-left? left-to-right? Not at all?
    foldrM fold ctx (zip es ts)
    where
      fold (el,t) acc = do
        t' <- substCtx acc t
        branch $ withCtx (const acc) $ check el t'

  -- Let<=
  -- NOTE: We should introduce a marker and remove new context-elements right of the marker to
  -- remove unnecessary existentials. But we'll need to generalize over the let-binding (in case
  -- it is a lambdas) to do this properly, otherwise the type of a let binding can have free
  -- existentials that would be removed. For now, we'll just keep all the cruft around.
  check' (Let p e1 e2) _ = do
    root $ "[Let<=]" <+> pretty e <+> "<=" <+> pretty ty
    (ty1, ctx') <- branch $ synthesize e1
    ty1s <- substCtx ctx' ty1 `decorateErr` (Other "[Let<=]")
    branch $ withCtx (const ctx') $ rule "Info" ("Let synthesized" <+> pretty ty1s <+> "for" <+> pretty p)
    case p of
      A _ (Bind nm) -> withCtx (const $ ctx' <+ ((LetB, nm) `HasType` ty1s)) $ branch $ check e2 ty
      _             -> snd <$> (withCtx (const ctx') $ branch $ checkClause ty1s (p, e2) ty)

  -- TypeApp<=
  -- check' (TypeApp ex arg) _ = do
  --   root $ "[TypeApp<=]" <+> pretty e <+> "<=" <+> pretty ty
  --   checkWfType arg
  --   _ <- asMonotypeTM arg
  --   (exty, theta) <- synthesize ex
  --   extys <- substCtx theta exty
  --   k' <- kindOf arg
  --   case extys of
  --     A _ (Forall af k faty)
  --       | k' == k -> ty `subtypeOf` subst arg af faty

  --     _           -> otherErr $ show $ pretty ex <+> "of type" <+> pretty exty <+> "cannot be applied to the type" <+> pretty arg

  -- Fixpoint<=
  -- an optimization really, since subsumption and Fixpoint=> can type the same
  check' (A _ (Prim Fix) `App` e2) _ = do
    rule "Fixpoint<=" (pretty e <+> "<=" <+> pretty ty)
    kappa <- freshName
    let kappat = A tann (TExists kappa)
    let fixty = A tann (A tann (Later kappat ty) :->: ty)
    withCtx (\g -> g <+ Exists kappa ClockK) $ branch $ check e2 fixty

  -- Sub
  check' _ _ = do
    rule "Sub" (pretty e <+> "<=" <+> pretty ty)
    (aty, theta) <- branch $ synthesize e
    atysubst <- substCtx theta aty `decorateErr` (Other "Sub.1")
    branch $ withCtx (const theta) $ rule "Info" ("Synthesized" <+> pretty atysubst <+> "for" <+> pretty e)
    btysubst <- substCtx theta ty `decorateErr` (Other "Sub.2")
    withCtx (const theta) $ branch $ atysubst `subtypeOf` btysubst

  sanityCheck ty0 = (do
    ctx <- getCtx
    _ <- wfContext ctx
    checkWfType ty0) `decorateErr` (Other $ show $ "Sanity check at" <+> pretty e <+> "<=" <+> pretty ty)

  -- just introduce forall-quantified variables as existentials
  -- in the current context
  intros :: Type a 'Poly -> TypingM a (Type a 'Poly, LocalCtx a)
  intros ty0@(A ann (Forall nm k t)) = do
    root $ "[Intros]" <+> pretty ty0
    ahat <- freshName
    let t' = subst (A ann $ TExists ahat) nm t
    withCtx (\g -> g <+ Exists ahat k) $ branch $ intros t'
  intros ty0 = do
    root $ "[Intros]" <+> pretty ty0
    ctx <- getCtx
    pure (ty0, ctx)

  -- Could be expressed as a fold, but this is a bit simpler methinks.
  -- Checks some clauses against an expected type.
  -- The marker is to make sure that the clauses can assign types to existentials
  -- that are in scope at the case-expr, but does not pollute the scope with new
  -- type variables that came into the context during the branch and body.
  -- TODO: move all the marker insertion logic here instead of in Case<=
  checkCaseClauses :: Name -> Type a 'Poly -> [(Pat a, Expr a)] -> Type a 'Poly -> TypingM a (LocalCtx a)
  checkCaseClauses markerName pty clauses expected =
    case clauses of
      (pat, expr) : clauses' -> do
        rule "CheckClause" ("|" <+> pretty pat <+> "->" <+> pretty expr <+> "<=" <+> pretty expected)
        (expected', ctx') <- checkClause pty (pat, expr) expected
        let nextCtx =  (dropTil (Marker markerName) ctx') <+ Marker markerName
        pty' <- substCtx ctx' pty -- more substCtx for (hopefully) better inference
        withCtx (const nextCtx) $
            checkCaseClauses markerName pty' clauses' expected'
      [] -> getCtx

  -- using substCtx alot improves inference. If the first clause infers that the pat is type P and
  -- body is type A, then subsequent patterns must also check against this more refined type.
  checkClause :: Type a 'Poly -> (Pat a, Expr a) -> Type a 'Poly -> TypingM a (Type a 'Poly, LocalCtx a)
  checkClause pty (pat, expr) expected = do
    ctx' <- branch $ checkPat pat pty
    expected' <- substCtx ctx' expected
    ctx'' <- withCtx (const ctx') $ branch $ check expr expected'
    expected'' <- substCtx ctx'' expected'
    pure (expected'', ctx'')

  -- here with no substCtx
  -- checkClause :: Type a 'Poly -> (Pat a, Expr a) -> Type a 'Poly -> TypingM a (LocalCtx a)
  -- checkClause pty (pat, expr) expected = do
  --   ctx' <- branch $ checkPat pat pty
  --   ctx'' <- withCtx (const ctx') $ branch $ check expr expected
  --   pure ctx''

synthesize :: Expr a -> TypingM a (Type a 'Poly, LocalCtx a)
synthesize expr@(A ann expr') = synthesize' expr' where
  -- Var
  synthesize' (Var nm) = do
    ctx <- getCtx
    fctx <- getFCtx
    case (nm `hasTypeInCtx` ctx <|> nm `hasTypeInFCtx` fctx) of
      Just ty -> do
        root $ "[Var]" <+> pretty expr <+> "=>" <+> pretty ty
        checkWfType ty *> pure (ty, ctx)

      Nothing -> root "[Var]" *> nameNotFound nm

  -- TickVar
  synthesize' (TickVar nm) =
    synthesize' (Var nm) `decorateErr` (Other "TickVar")

  -- Anno
  synthesize' (Ann e ty) = do
    root $ "[Anno]" <+> pretty e <+> ":" <+> pretty ty
    _ <- branch $ check e ty
    (ty, ) <$> getCtx

  -- ->I=> (with generalization)
  synthesize' (Lam x Nothing e) = do
    root $ "[->I=>]" <+> pretty expr
    markerName <- freshName
    alpha <- freshName
    beta <- freshName
    let alphac = Exists alpha Star
        betac  = Exists beta Star
        alphat = A ann $ TExists alpha
        betat  = A ann $ TExists beta
        mrker = Marker markerName
    ctx' <- withCtx (\g -> g <+ mrker <+ alphac <+ betac <+ (LamB, x) `HasType` alphat) $ branch (check e betat)
    (delta, _, delta') <- splitCtx mrker ctx'
    let rty = A ann $ alphat :->: betat
    tau <- substCtx ctx' rty `decorateErr` (Other "in [->I=>]")
    let unsolved = getUnsolved delta'
    let tausubst = foldr (\(x, _k) acc -> subst (A ann $ TVar x) x acc) tau unsolved
    let quanted = foldr (\(x, k) acc -> A ann $ Forall x k acc) tausubst unsolved
    root $ "[Info] generalized" <+> pretty tau <+> "to" <+> pretty quanted
    pure (quanted, delta)

  -- -- ->I=> (without generalization)
  -- synthesize' (Lam x Nothing e) = do
  --   root $ "[->I=>]" <+> pretty expr
  --   alpha <- freshName
  --   beta <- freshName
  --   let alphac = Exists alpha Star
  --       betac  = Exists beta Star
  --       alphat = A ann $ TExists alpha
  --       betat  = A ann $ TExists beta
  --   ctx' <- withCtx (\g -> g <+ alphac <+ betac <+ (LamB, x) `HasType` alphat) $ branch (check e betat)
  --   (delta, _, theta) <- splitCtx ((LamB, x) `HasType` alphat) ctx'
  --   pure (A ann $ alphat :->: betat, delta)

  -- ->AnnoI=>
  synthesize' (Lam x (Just argty) e) = do
    root $ "[->AnnoI=>]" <+> pretty expr
    beta <- freshName
    let betac  = Exists beta Star
        betat  = A ann $ TExists beta
    let ce = (LamB, x) `HasType` argty
    ctx' <- withCtx (\g -> g <+ betac <+ ce) $ branch (check e betat)
    (delta, _, _) <- splitCtx ce ctx'
    pure (A ann $ argty :->: betat, delta)

  -- PrimRec=>
  synthesize' (PrimRec prty) = do
    rule "PrimRec=>" (pretty expr)
    errIf (kindOf prty) (/= (Star :->*: Star)) (const $ Other $ show $ "Expected" <+> pretty prty <+> "to have kind * -> *")
    assertFunctor prty
    let ?annotation  = ann
    let resultty     = H.tvar "A"
    let ftorty       = prty
    let resultq      = H.forAll ["A"]
    let inductivet   = A ann $ RecTy ftorty
    let ftorresultty = ftorty `H.tapp` H.ttuple [inductivet, resultty]
    let body         = ftorresultty `H.arr` resultty
    ctx <- getCtx
    pure (resultq $ body `H.arr` inductivet `H.arr` resultty, ctx)

   -- Fmap=>
  synthesize' (Fmap fmapty) = do
    rule "Fmap=>" (pretty expr)
    errIf (kindOf fmapty) (/= (Star :->*: Star)) (const $ Other $ show $ "Expected" <+> pretty fmapty <+> "to have kind * -> *")
    assertFunctor fmapty
    let ?annotation  = ann
    ctx <- getCtx
    let av = H.tvar "a"
        bv = H.tvar "b"
    pure (H.forAll ["a", "b"] $ (av `H.arr` bv) `H.arr` (fmapty `H.tapp` av) `H.arr` (fmapty `H.tapp` bv), ctx)

  -- ->E
  synthesize' (e1 `App` e2) = do
    rule "->E" (pretty expr)
    (ty1, theta) <- branch $ synthesize e1
    ty1subst <- substCtx theta ty1 `decorateErr` (Other "[->E]")
    withCtx (const theta) $ branch $ applysynth ty1subst e2

  -- Prim=>
  synthesize' (Prim p) = do
    (pt, theta) <- inferPrim ann p
    root $ "[Prim=>]" <+> pretty expr <+> "=>" <+> pretty pt
    pure (pt, theta)

  -- Case=>
  synthesize' (Case e clauses) = do
    root $ "[Case=>]" <+> pretty e <+> enclose "[" "]" (cat $ map pretty clauses)
    cannotSynthesize expr

  -- Let=>
  synthesize' (Let p e1 e2) = do
    root $ "[Let=>]" <+> pretty expr <+> "=>" 
    (e1ty, theta) <- branch $ synthesize e1
    e1tys <- substCtx theta e1ty
    theta' <- withCtx (const theta) $ branch $ checkPat p e1tys
    withCtx (const theta') $ branch $ synthesize e2

  -- Tuple=>
  synthesize' (Tuple es) = do
    root $ "[Tuple=>]" <+> pretty expr
    ctx <- getCtx
    (ts, ctx') <- foldrM folder ([], ctx) es
    pure (A ann $ TTuple ts, ctx')
    where
      folder e (ts', acc) = do
        (t', acc') <- branch $ withCtx (const acc) $ synthesize e
        pure (t' : ts', acc')

  -- TickAbs=>
  synthesize' (TickAbs nm k e) = do
    root $ "[TickAbs=>]" <+> pretty expr
    let kt = A ann $ TVar k
    let c = (LamB, nm) `HasType` kt
    (ety, ctx') <- withCtx (\g -> g <+ c) $ branch $ synthesize e
    ety' <- substCtx ctx' ety
    (delta, _, _) <- splitCtx c ctx'
    let lty = A ann $ Later kt ety'
    pure (lty, delta)

  -- TypeApp=>
  synthesize' (TypeApp ex arg) = do
    root $ "[TypeApp=>]" <+> pretty expr
    (exty, theta) <- branch $ synthesize ex
    extys <- substCtx theta exty
    checkWfType arg
    -- _ <- asMonotypeTM arg
    k' <- kindOf arg
    case extys of
      A _ (Forall af k faty)
        | k' == k -> pure (subst arg af faty, theta)

      _           -> otherErr $ show $ pretty ex <+> "of type" <+> pretty exty <+> "cannot be applied to the type" <+> pretty arg <+> "of kind" <+> pretty k'


  synthesize' _ = cannotSynthesize expr

  -- assertLater t = do
  --   rule "AssertLater" (pretty t)
  --   kappa <- freshName

  --   alpha <- freshName
  --   let kappat = A ann $ TExists kappa
  --   let alphat  = A ann $ TExists alpha
  --   let lt = A ann (Later kappat alphat)
  --   theta <- branch $ withCtx (\g -> g <+ Exists kappa ClockK <+ Exists alpha Star) $ t `subtypeOf` lt
  --   kappat' <- substCtx theta kappat
  --   alphat' <- substCtx theta alphat
  --   pure (kappat', alphat', theta)

inferPrim :: a -> Prim -> TypingM a (Type a 'Poly, LocalCtx a)
inferPrim ann p = case p of
  Unit   -> (A ann (TFree $ UName "Unit"), ) <$> getCtx
  Integer _  -> (A ann (TFree $ UName "Int"), ) <$> getCtx
  Undefined -> (A ann $ Forall "a" Star (A ann $ TVar "a"), ) <$> getCtx

  -- TODO: The tick constant unifies with any clock variable?
  Tick   -> do
    alpha <- freshName
    ctx' <- (\g -> g <+ Exists alpha ClockK) <$> getCtx
    pure (A ann $ TExists alpha, ctx')

  -- Fold=>
  Fold   -> do
    ctx <- getCtx
    let a1 = UName "f"
    let a1t = A ann (TVar a1)
    let folded = A ann $ RecTy a1t
    let unfolded = A ann $ a1t `TApp` folded
    let arr = A ann (unfolded :->: folded)
    let quanted = A ann (Forall a1 (Star :->*: Star) arr)
    pure (quanted, ctx)

  -- Unfold=>
  Unfold -> do
    ctx <- getCtx
    let a1 = UName "f"
    let a1t = A ann (TVar a1)
    let folded = A ann $ RecTy a1t
    let unfolded = a1t `tapp` folded
    let arr = folded --> unfolded
    pure (fall a1 (Star :->*: Star) arr, ctx)

  -- PrimRec -> do
  --   let resultty = tv "A"
  --   let ftorty = tv "F"
  --   let ftorq = fall "F" (Star :->*: Star)
  --   let resultq = fall "A" Star
  --   let inductivet = A ann $ RecTy ftorty
  --   let ftorresultty = ftorty `tapp` ttuple [inductivet, resultty]
  --   let body = ftorresultty --> resultty
  --   ctx <- getCtx
  --   pure (ftorq . resultq $ body --> inductivet --> resultty, ctx)

  Fix -> do
    let ltr k = A ann . Later k
    let kappa = tv "k"
    let at = tv "a"
    let aq = fall "a" Star
    let kq = fall "k" ClockK
    ctx <- getCtx
    pure (kq . aq $ (ltr kappa at --> at) --> at, ctx)

  where
    infixr 9 -->
    x --> y = A ann (x :->: y)
    fall n k = A ann . Forall n k
    tv = A ann . TVar . UName
    tapp t1 = A ann . TApp t1
    ttuple = A ann . TTuple


-- check that patterns type-check and return a new ctx extended with bound variables
checkPat :: Pat a -> Type a 'Poly -> TypingM a (LocalCtx a)
checkPat pat@(A ann p) ty = do
  ctx <- getCtx
  dctx <- getDCtx
  rule "CheckPat" (pretty pat <+> "<=" <+> pretty ty)
  case p of
    Bind nm -> pure $ ctx <+ (LetB, nm) `HasType` ty

    Match nm pats -> case query nm dctx of
      Nothing    -> otherErr $ "Pattern " ++ show nm ++ " not found in context."
      Just destr -> branch $ checkDestr destr pats ty

    PTuple pats -> 
      -- generate a tuple destructor of length (length pats)
      let plen = genericLength pats
          dname = UName $ "tuple_" ++ show plen
          dbound = map (\x -> (DeBruijn x, Star)) [0 .. (plen - 1)]
          dargs = map (A ann . TVar . fst) dbound
          dtyp = A ann $ TTuple $ dargs
          d = Destr {name = dname, bound = dbound, typ = dtyp, args = dargs}
      in  branch $ checkDestr d pats ty

-- Take a destructor and "existentialize it" - replace its bound type-variables
-- with fresh existentials
existentialize :: forall a. a -> Destr a -> TypingM a (LocalCtx a, Destr a)
existentialize ann destr = do
  (nms, destr') <- foldrM folder ([], destr) (bound destr)
  ctx <- getCtx
  let ctx' = foldr (\(n,k) g -> g <+ Exists n k) ctx nms
  pure (ctx', destr')
  where
    folder (b,k) (nms, d@(Destr {typ, args})) = do
      b' <- freshName
      let s = subst (A ann $ TExists b') b
      let ntyp = s typ
      let nargs = map s args
      pure $ ((b',k) : nms, d {typ = ntyp, args = nargs})


-- in a context, check a destructor against a list of patterns and an expected type.
-- if it succeeds, it binds the names listed in the pattern match to the input context
checkDestr :: Destr a -> [Pat a] -> Type a 'Poly -> TypingM a (LocalCtx a)
checkDestr d@(Destr {name, args}) pats expected@(A ann _)
  | length pats /= length args =
      otherErr $ show $ "Expected" <+> pretty (length args)
             <+> "arguments to" <> pretty name <+> "but got" <+> pretty (length pats)
  | otherwise                  = do
      (delta, Destr {typ = etyp, args = eargs}) <- existentialize ann d
      ctx' <- withCtx (const delta) $ branch $ etyp `subtypeOf` expected
      foldlM folder ctx' $ zip pats eargs
      where
        folder acc (p, t) = do
          t' <- substCtx acc t `decorateErr` (Other $ show $ "substCtx" <+> pretty acc <+> pretty t)
          withCtx (const acc) $ checkPat p t'

applysynth :: forall a. Type a 'Poly -> Expr a -> TypingM a (Type a 'Poly, LocalCtx a)
applysynth ty@(A tann ty') e@(A _ e') = applysynth' ty' e' where
  -- ∀App
  applysynth' (Forall alpha k aty) _ = do
    rule "∀App" (pretty ty <+> "•" <+> pretty e)
    -- fresh name to avoid clashes
    alpha' <- freshName
    let atysubst = subst (texists alpha') alpha aty
    withCtx (\g -> g <+ Exists alpha' k) $ branch $ applysynth atysubst e

  -- |>καApp
  applysynth' (TExists alpha) (TickVar _tv) =
    let articulate a1 a2 =
          let articulated = A tann $ Later (texists a1) (texists a2)
          in  [Exists a2 Star, Exists a1 ClockK, alpha := articulated]
    in  appsynthexists alpha "|>καApp" articulate

  -- αApp
  applysynth' (TExists alpha) _ =
    let articulate a1 a2 =
          let articulated = A tann (texists a1 :->: texists a2)
          in  [Exists a2 Star, Exists a1 Star, alpha := articulated]
    in  appsynthexists alpha "αApp" articulate

  -- |>κApp⋄
  applysynth' (Later kappat cty) (Prim Tick) = do
    rule "TickApp" (pretty ty <+> "•" <+> pretty e)
    kappa <- fromEither $ extractKappa kappat
    ctx <- getCtx
    ctx `mustBeStableUnder` kappa
    pure (cty, ctx)

  -- |>κApp
  applysynth' (Later kappat cty) _ = do
    rule "TickVarApp" (pretty ty <+> "•" <+> pretty e)
    (cty,) <$> branch (check e kappat)

  -- ->App
  applysynth' (aty :->: cty) _ = do
    rule "->App" (pretty ty <+> "•" <+> pretty e)
    (cty,) <$> branch (check e aty)

  applysynth' _ _ = root "[CannotAppSynthesize]" *> cannotAppSynthesize ty e

  appsynthexists alpha ruleName toInsert = do
    ctx <- getCtx
    rule ruleName (pretty ty <+> "•" <+> pretty e)
    if ctx `containsEVar` alpha
      then do
        a1 <- freshName; a2 <- freshName
        -- alphak <- queryKind alpha
        ctx' <- insertAt (Exists alpha Star) (toInsert a1 a2)
        delta <- branch $ withCtx (const ctx') $ check e (texists a1)
        pure (texists a2, delta)
      else
        nameNotFound alpha

  texists :: Name -> Type a s
  texists = A tann . TExists

