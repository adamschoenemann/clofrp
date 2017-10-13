{-| Implementation of Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism 
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
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}

module CloTT.Check.Poly
  ( module CloTT.Check.Poly
  , module CloTT.Check.Poly.Destr
  , module CloTT.Check.Poly.Contexts
  , module CloTT.Check.Poly.TypingM
  )
  where

import Data.Foldable (foldlM, foldrM)
import Debug.Trace
import Data.String (fromString)
import Control.Applicative ((<|>))
import Control.Monad.Except (catchError, throwError)
import Data.Text.Prettyprint.Doc
import Data.List (find)
import Data.Maybe (isJust)

import CloTT.AST.Name
import CloTT.Context
import CloTT.Annotated
import CloTT.AST.Parsed hiding (exists)
import CloTT.Pretty
import CloTT.Check.Poly.Destr
import CloTT.Check.Poly.Contexts
import CloTT.Check.Poly.TypingM


runSubtypeOf0 :: Type a 'Poly -> Type a 'Poly -> TypingMRes a (TyCtx a)
runSubtypeOf0 t1 t2 = runSubtypeOf initRead t1 t2

runSubtypeOf :: TypingRead a -> Type a 'Poly -> Type a 'Poly -> TypingMRes a (TyCtx a)
runSubtypeOf rd t1 t2 = runTypingM (t1 `subtypeOf` t2) rd initState

runCheck0 :: Expr a -> Type a 'Poly -> TypingMRes a (TyCtx a)
runCheck0 e t = runCheck initRead e t

runCheck :: TypingRead a -> Expr a -> Type a 'Poly -> TypingMRes a (TyCtx a)
runCheck rd e t = runTypingM (check e t) rd initState

runSynth :: TypingRead a -> Expr a -> TypingMRes a (Type a Poly, TyCtx a)
runSynth rd e = runTypingM (synthesize e) rd initState


substCtx' :: TyCtx a -> Type a Poly -> Either Name (Type a Poly)
substCtx' ctx (A a ty) = 
  case ty of
    TFree x -> pure $ A a $ TFree x
    TVar x  -> pure $ A a $ TVar  x
    TExists x -> 
      case findAssigned x ctx of
        Just tau -> substCtx' ctx (asPolytype tau) -- do it again to make substitutions simultaneous (transitive)
        Nothing
          | Exists x `isInContext` ctx -> pure $ A a $ TExists x
          | otherwise                  -> Left x

    t1 `TApp` t2 -> do
      t1' <- substCtx' ctx t1
      t2' <- substCtx' ctx t2
      pure $ A a $ t1' `TApp` t2'
    
    t1 :->: t2 -> do
      t1' <- substCtx' ctx t1
      t2' <- substCtx' ctx t2
      pure $ A a $ t1' :->: t2'
    
    Forall x t -> do
      t' <- substCtx' ctx t
      pure $ A a $ Forall x t'

    Clock x t -> do
      t' <- substCtx' ctx t
      pure $ A a $ Clock x t'

    RecTy t -> do
      t' <- substCtx' ctx t
      pure $ A a $ RecTy t'


substCtx :: TyCtx a -> Type a Poly -> TypingM a (Type a Poly)
substCtx ctx ty = 
  case substCtx' ctx ty of
    Left x -> otherErr $ "existential " ++ show x ++ " not in context during substitution"
    Right ctx' -> pure ctx'


splitCtx :: CtxElem a -> TyCtx a -> TypingM a (TyCtx a, CtxElem a, TyCtx a)
splitCtx el ctx =
  case splitCtx' el ctx of
    Nothing -> root "splitCtx" *> cannotSplit el ctx
    Just x  -> do 
      -- traceM $ "splitCtx " ++ show el ++ ":  " ++ show ctx ++ " ---> " ++ show x
      pure x

before :: CtxElem a -> CtxElem a -> TypingM a Bool
before alpha beta = before' alpha beta <$> getCtx


insertAt :: CtxElem a -> TyCtx a -> TypingM a (TyCtx a)
insertAt at insertee = do
  ctx <- getCtx
  case insertAt' at insertee ctx of
    Nothing   -> otherErr $ "Cannot insert into context " ++ show ctx ++ " at " ++ show at
    Just ctx' -> pure ctx'

-- Infer the kind of a type variable from how it is used in a type
-- Its not gonna work, I think though... Instead, "spine-ify" first and
-- then filter
-- inferVarKind :: KindCtx a -> Name -> Type a Poly -> Either String Kind
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


kindOf :: Type a Poly -> TypingM a Kind
kindOf (A _ t) = do
  kctx <- getKCtx
  ctx <- getCtx
  case t of
    TFree v -> maybe (notFound v) pure $ query v kctx
    
    -- TODO: should look up kind in local kctx
    TVar v 
      | ctx `containsTVar` v -> pure Star
      | otherwise            -> notFound v

    -- TODO: should look up kind in local kctx
    -- I have a hack in place, where, iff the existential is already assigned
    -- I infer its kind from its assigned type
    TExists  v -> do
      case findAssigned v ctx of
        Just mty -> withCtx (dropTil (v := mty)) $ kindOf (asPolytype mty)
        Nothing 
          | ctx `containsEVar` v -> pure Star
          | otherwise            -> notFound v

    TApp t1 t2 -> do
      k1 <- kindOf t1
      k2 <- kindOf t2
      case (k1, k2) of
        (k11 :->*: k12, k2')
          | k11 == k2' -> pure k12
          | otherwise  -> 
              otherErr $ "Expected " ++ pps t2 ++ " to have kind " ++ pps k11
        (_k1', _) -> otherErr $ "Expected " ++ pps t1 ++ " to be a type constructor"

    t1 :->: t2 -> do
      k1 <- kindOf t1
      k2 <- kindOf t2
      case (k1, k2) of
        (Star, Star) -> pure Star
        (k1', k2')   -> otherErr $ "Both operands in arrow types must have kind *, but had " 
                     ++ pps k1' ++ " and " ++ pps k2' ++ " in " ++ pps t
    
    Forall v tau -> withCtx (\g -> g <+ Uni v) $ kindOf tau

    -- TODO: what to do with v here?
    Clock  v tau -> kindOf tau
    -- TODO: what to do with v here?
    RecTy tau -> do 
      k <- kindOf tau
      case k of
        Star :->*: Star -> pure Star
        _               -> otherErr $ show $ pretty tau <+> "must have kind * -> * to be an argument to Fix" 
      

  where
    notFound = nameNotFound

-- A type is wellformed
-- this one, validType and kindOf should probably be merged somehow...
checkWfType :: Type a Poly -> TypingM a ()
checkWfType ty@(A ann ty') = do
  kctx <- getKCtx
  ctx <- getCtx
  case ty' of
    -- UFreeWF
    TFree x
      | x `isMemberOf` kctx -> pure ()
      | otherwise           -> notWfType ty

    -- UVarWF
    TVar x 
      | Just _ <- ctxFind (varPred x) ctx -> pure ()
      | otherwise                         -> notWfType ty

    -- EvarWF and SolvedEvarWF
    TExists alpha 
      | Just _ <- ctxFind (expred $ alpha) ctx -> pure ()
      | otherwise                              -> notWfType ty

    -- ArrowWF
    t1 :->: t2 -> do 
      errIf (kindOf t1) (/= Star) (const $ Other $ show $ pretty t1 <+> "must have kind *")
      errIf (kindOf t2) (/= Star) (const $ Other $ show $ pretty t2 <+> "must have kind *")
      checkWfType t1 *> checkWfType t2

    -- ForallWF
    Forall x t 
      | Just _ <- ctxFind (varPred x) ctx -> otherErr $ show $ pretty x <+> "is already in context"
      | otherwise                         -> withCtx (\g -> g <+ Uni x) $ checkWfType t

    -- TAppWF. FIXME Should check correct kinds as well.
    TApp t1 t2 -> do
      -- errIf (kindOf t1) (== Star) (const $ Other $ show $ pretty t1 <+> "must be a type-constructor")
      checkWfType t1 *> checkWfType t2

    -- ClockWF
    Clock kappa t -> do
      clks <- getCCtx
      if kappa `isMemberOf` clks
        then otherErr $ show $ pretty kappa <+> "is already in clock-context"
        else withCCtx (extend kappa ()) $ checkWfType t

    RecTy t -> checkWfType t

  where 
    expred alpha = \case
      Exists alpha' -> alpha == alpha'
      alpha' := _   -> alpha == alpha' 
      _         -> False

    varPred x = \case
      Uni x' -> x == x'
      _      -> False

-- Check if a context is well-formed
-- will completely ignore trCtx in the TypingM monad
-- TODO: Also fail ctx such as [a := tau, a] or [a, a := tau]
wfContext :: forall a. TyCtx a -> TypingM a ()
wfContext (Gamma elems) = foldrM fn [] elems *> pure () where
  fn :: CtxElem a -> [CtxElem a] -> TypingM a [CtxElem a]
  fn el acc = do 
    _ <- withCtx (const $ Gamma acc) $ checkIt el 
    pure (el : acc)

  elem' f xs = isJust $ find (\x -> f (unann x)) xs

  -- this one refers to ctx through getCtx
  checkIt el = case el of
    Uni nm          -> notInDom nm el
    Exists nm       -> notInDom nm el
    nm `HasType` ty -> notInDom nm el *> checkWfType (asPolytype ty)
    nm := ty        -> notInDom nm el *> checkWfType (asPolytype ty)
    Marker nm       -> do 
      _ <- notInDom nm el 
      Gamma ctx <- getCtx
      if ((\x -> Marker nm == x) `elem'` ctx)
        then notWfContext (Marker nm) 
        else pure ()

  -- TODO: fix this to account for HasType constructor as well
  notInDom nm el = do
    Gamma ctx <- getCtx
    if (\x -> Uni nm == x || Exists nm == x) `elem'` ctx
      then notWfContext el
      else pure ()

validType :: KindCtx a -> Type a Poly -> TypingM a ()
validType kctx t = do
  k <- withKCtx (const kctx) $ kindOf t
  case k of
    Star -> pure ()
    _    -> otherErr $ show $ pretty t <+> "has kind" <+> pretty k <+> "but expected *"

-- assign an unsolved variable to a type in a context
-- TODO: Optimize 
assign :: Name -> Type a Mono -> TypingM a (TyCtx a)
assign nm ty = do
  ctx@(Gamma xs) <- getCtx
  if isAssigned nm ctx
    then otherErr $ show $ pretty nm <+> "is already assigned"
    else 
      case foldr fn ([], False) xs of
        (xs', True) -> do
          _ <- wfContext (Gamma xs')
          pure (Gamma xs')
        (xs', False) -> otherErr $ show $ pretty nm <+> ":=" <+> pretty ty <+> "Didn't assign anything" 
      where
        fn (Exists nm') (xs, _) | nm == nm' = (nm := ty : xs, True)
        fn x (xs, b)                        = (x : xs, b)

asMonotypeTM :: Type a s -> TypingM a (Type a Mono)
asMonotypeTM = maybe (otherErr "asMonotype") pure . asMonotype

-- Under input context Γ, instantiate α^ such that α^ <: A, with output context ∆
instL :: Name -> Type a Poly -> TypingM a (TyCtx a)
-- InstLSolve
instL ahat ty@(A a ty') = 
  let solve = do
        ctx <- getCtx
        root $ "[InstLSolve]" <+> pretty ty <+> ":<=" <+> pretty ahat <+> "in" <+> pretty ctx
        mty <- asMonotypeTM ty
        ctx' <- assign ahat mty 
        pure ctx'
  in solve `catchError` \err -> 
      case ty' of
        -- InstLReach
        TExists bhat -> do
          root $ "[InstLReach]" <+> "^" <> pretty bhat <+> "=" <+> "^" <> pretty ahat
          Exists ahat `before` Exists bhat >>= \case
            True -> assign bhat (A a $ TExists ahat)
            False -> otherErr $ "[InstLReach] error"

        -- InstLArr
        t1 :->: t2 -> do
          ctx <- getCtx
          root $ "[InstLArr]" <+> pretty ahat <+> ":<=" <+> pretty ty <+> "in" <+> pretty ctx
          af1 <- freshName
          af2 <- freshName
          let ahat1 = exists af1
          let ahat2 = exists af2
          let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
          ctx' <- insertAt (exists ahat) $ mempty <+ ahat1 <+ ahat2 <+ ahat := arr
          omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
          substed <- substCtx omega t2
          r <- withCtx (const omega) $ branch (af2 `instL` substed)
          pure r
        
        -- InstLAllR
        Forall beta bty -> do
          ctx <- getCtx
          root $ "[InstLAllR]" <+> pretty ahat <+> ":<=" <+> pretty bty <+> "in" <+> pretty ctx
          beta' <- freshName
          let bty' = subst (A a $ TFree beta') beta bty
          ctx' <- withCtx (\g -> g <+ uni beta') $ branch (ahat `instL` bty')
          (delta, _, delta') <- splitCtx (uni beta') ctx'
          pure delta

        -- InstLTApp. Identical to InstLArr
        TApp t1 t2 -> do
          root $ "[InstLTApp]" <+> pretty ahat <+> ":<=" <+> pretty ty
          af1 <- freshName
          af2 <- freshName
          let ahat1 = exists af1
          let ahat2 = exists af2
          let app = A a $ (A a $ TExists af1) `TApp` (A a $ TExists af2)
          ctx' <- insertAt (exists ahat) (mempty <+ ahat1 <+ ahat2 <+ ahat := app)
          omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
          substed <- substCtx omega t2
          r <- withCtx (const omega) $ branch (af2 `instL` substed)
          pure r

        -- InstLRec
        RecTy t -> do
          root $ "[InstLRec]" <+> pretty ahat <+> ":<=" <+> pretty ty
          a1 <- freshName
          let rt = A a $ RecTy (A a $ TExists a1)
          ctx' <- insertAt (exists ahat) (mempty <+ Exists a1 <+ ahat := rt)
          withCtx (const ctx') $ branch (a1 `instL` t)
        
        _ -> do
          root $ "[InstLError]" <+> "^" <> pretty ahat <+> "=" <+> pretty ty
          throwError err


instR :: Type a Poly -> Name -> TypingM a (TyCtx a)
-- InstRSolve
instR ty@(A a ty') ahat = 
  let solve = do
        mty <- asMonotypeTM ty
        ctx' <- assign ahat mty 
        root $ "[InstRSolve]" <+> pretty ty <+> "=<:" <+> pretty ahat
        pure ctx'
  in  solve `catchError` \err ->
        case ty' of
          -- InstRReach
          TExists bhat -> do 
            root $ "[InstRReach]" <+> "^" <> pretty ahat <+> "=" <+> "^" <> pretty bhat
            Exists ahat `before` Exists bhat >>= \case
              True -> assign bhat (A a $ TExists ahat)
              False -> otherErr $ "[InstRReachError]"

          -- InstRArr
          t1 :->: t2 -> do
            root $ "InstRArr"
            af1 <- freshName
            af2 <- freshName
            let ahat1 = exists af1
            let ahat2 = exists af2
            let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
            ctx' <- insertAt (exists ahat) (mempty <+ ahat1 <+ ahat2 <+ ahat := arr)
            omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r
          
          -- InstRAllL
          Forall beta bty -> do
            root $ "[InstRAllL]"
            beta' <- freshName
            let substedB = subst (A a $ TExists beta') beta bty
            ctx' <- withCtx (\g -> g <+ marker beta' <+ exists beta') $ branch (substedB `instR` ahat)
            (delta, _, delta') <- splitCtx (marker beta') ctx'
            pure delta
          
          -- InstRTApp. Identical to InstRArr
          TApp t1 t2 -> do
            ctx <- getCtx
            root $ "[InstRTApp]" <+> pretty ty <+> "=<:" <+> pretty ahat <+> "in" <+> pretty ctx
            af1 <- freshName
            af2 <- freshName
            let ahat1 = exists af1
            let ahat2 = exists af2
            let app = A a $ (A a $ TExists af1) `TApp` (A a $ TExists af2)
            ctx' <- insertAt (exists ahat) (mempty <+ ahat1 <+ ahat2 <+ ahat := app)
            omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          -- InstRRec
          RecTy t -> do
            root $ "[InstRRec]" <+> pretty ty <+> "=<:" <+> pretty ahat
            a1 <- freshName
            let rt = A a $ RecTy (A a $ TExists a1)
            ctx' <- insertAt (exists ahat) (mempty <+ Exists a1 <+ ahat := rt)
            withCtx (const ctx') $ branch (t `instR` a1)
          
          _ -> do
            ctx <- getCtx
            root $ "[InstRError]" <+> "^" <> pretty ahat <+> "=" <+> pretty ty <+> "in" <+> pretty ctx
            throwError err
            -- otherErr $ showW 80 $ "[instR] Cannot instantiate" <+> pretty ahat <+> "to" <+> pretty ty <+> ". Cause:" <+> fromString err

-- Under input context Γ, type A is a subtype of B, with output context ∆
-- A is a subtype of B iff A is more polymorphic than B
subtypeOf :: Type a Poly -> Type a Poly -> TypingM a (TyCtx a)
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
            if Uni x `isInContext` ctx
              then root ("[<:Var]" <+> pretty ty1 <+> "<:" <+> pretty ty2) *> getCtx
              else root ("[<:Var]") *> otherErr ("universal variable " ++ show x ++ " not found.")
        | otherwise = 
            root ("[<:Var]" <+> pretty ty1 <+> "<:" <+> pretty ty2) *> cannotSubtype ty1 ty2
  
  -- <:Exvar
  subtypeOf' (TExists a) (TExists a')
    | a == a' = do 
      ctx <- getCtx
      root $ "[<:Exvar]" <+> pretty ty1 <+> "<:" <+> pretty ty2
      if Exists a `isInContext` ctx
        then pure ctx
        else branch $ nameNotFound a

  -- <:->
  subtypeOf' (a1 :->: a2) (b1 :->: b2) = do
    root $ "[<:->]" <+> pretty ty1 <+> "<:" <+> pretty ty2
    ctx' <- branch (b1 `subtypeOf` a1)
    a2' <- substCtx ctx' a2
    b2' <- substCtx ctx' b2
    r <- withCtx (const ctx') $ branch (a2' `subtypeOf` b2')
    pure r

  -- <:∀R
  subtypeOf' t1 (Forall a (A ann t2)) = do
    a' <- freshName
    ctx <- getCtx
    root $ "[<:∀R]" <+> pretty ty1 <+> "<:" <+> pretty ty2 <+> "in" <+> pretty ctx
    let ty2' = subst (A ann $ TVar a') a (A ann $ t2)
    ctx' <- withCtx (\g -> g <+ uni a') $ branch (ty1 `subtypeOf` ty2')
    pure $ dropTil (uni a') ctx'

  -- <:∀L
  subtypeOf' (Forall nm (A at1 t1)) _ = do
    ctx <- getCtx
    root $ "[<:∀L]" <+> pretty ty1 <+> "<:" <+> pretty ty2 <+> "in" <+> pretty ctx
    nm' <- freshName
    let t1' = subst (A at1 $ TExists nm') nm (A at1 t1)
    ctx' <- withCtx (\g -> g <+ marker nm' <+ exists nm') $ branch (t1' `subtypeOf` ty2)
    pure $ dropTil (marker nm') ctx'
  
  -- <:InstantiateL
  subtypeOf' (TExists ahat) _
    | ahat `inFreeVars` ty2 = root "[InstantiateL] OccursError!" *> occursIn ahat ty2
    | otherwise = do 
        ctx <- getCtx
        root $ "[InstantiateL]" <+> "^" <> pretty ahat <+> ":<=" <+> pretty ty2 <+> "in" <+> pretty ctx
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
  
  -- <:TApp
  subtypeOf' (TApp a1 a2) (TApp b1 b2) = do
    ctx <- getCtx
    root $ "[<:TApp]" <+> pretty ty1 <+> "<:" <+> pretty ty2 <+> "in" <+> pretty ctx
    theta <- branch $ a1 `subtypeOf` b1
    a2' <- substCtx theta a2
    b2' <- substCtx theta b2
    branch $ withCtx (const theta) $ a2' `subtypeOf` b2'
  
  -- <:Rec
  subtypeOf' (RecTy b1) (RecTy b2) = do
    root $ "[<:Rec]" <+> pretty ty1 <+> "<:" <+> pretty ty2
    branch $ b1 `subtypeOf` b2

  subtypeOf' t1 t2 = do
    -- root $ "[SubtypeError!]" <+> (fromString . show . unann $ t1) <+> "<:" <+> (fromString . show . unann $ t2)
    root $ "[SubtypeError!]" <+> pretty t1 <+> "<:" <+> pretty t2
    cannotSubtype ty1 ty2

check :: Expr a -> Type a Poly -> TypingM a (TyCtx a)
check e@(A eann e') ty@(A tann ty') = sanityCheck ty *> check' e' ty' where

  -- 1I (PrimI)
  check' (Prim p) _ = do
    root "[PrimI]"
    pty <- A eann <$> inferPrim p
    branch $ ty `subtypeOf` pty
  
  -- ∀I
  check' _ (Forall alpha aty) = do
    ctx <- getCtx
    root $ "[∀I]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
    alpha' <- freshName
    let alphat = A tann $ TVar alpha'
    let aty' = subst alphat alpha aty
    -- FIXME: We need to traverse e and substitute alpha for a fresh name in order to make type annotations
    -- with type variables work. This is horribly ineffecient, but will do for now
    let esubst = substTVarInExpr alphat alpha e
    (delta, _, _) <- splitCtx (Uni alpha') =<< withCtx (\g -> g <+ Uni alpha') (branch $ check esubst aty')
    pure delta
  
  -- ->I
  check' (Lam x Nothing e2) (aty :->: bty) = do
    ctx <- getCtx
    root $ "[->I]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
    let c = x `HasType` aty
    (delta, _, _) <- splitCtx c =<< withCtx (\g -> g <+ c) (branch $ check e2 bty)
    pure delta
  
  -- Case<=
  check' (Case on clauses) _ = do
    root $ "[Case<=]" <+> pretty e <+> "<=" <+> pretty ty
    (pty, delta) <- branch $ synthesize on
    (pty', delta') <- withCtx (const delta) $ branch $ intros pty
    markerName <- freshName
    cty <- withCtx (const $ delta' <+ Marker markerName) $ branch $ checkCaseClauses markerName pty' clauses ty
    pure delta
  
  -- ClockAbs
  check' (ClockAbs k body) (Clock k' t)
    | k == k' = do
        root "[ClockAbs]"
        (k `isMemberOf`) <$> getCCtx >>= \case
          True -> otherErr $ show $ pretty k <+> "is already in clock context"
          _     -> do 
            -- alpha rename
            kappa <- freshName
            let tsubst    = subst (A tann $ TVar kappa) k t
            let bodysubst = substClockVarInExpr (A eann $ ClockVar kappa) k body
            withCCtx (\g -> extend kappa () g) $ branch $ check bodysubst tsubst
    | otherwise = do 
        root "[ClockAbs]"
        otherErr $ show $ "Clock" <+> pretty k <+> "must be named" <+> pretty k'
  
  -- FoldApp
  -- check' (A fann (Prim Fold) `App` e2) _ = do
  --   ctx <- getCtx
  --   root $ "[FoldApp]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
  --   fex <- freshName
  --   let fext = A tann $ TExists fex
  --   let recTy = A tann $ RecTy fext
  --   delta <- withCtx (\g -> g <+ Exists fex) $ ty `subtypeOf` recTy
  --   tysubst <- substCtx delta ty
  --   case tysubst of 
  --     A rann (RecTy fun) -> withCtx (const delta) $ check e2 (A tann $ fun `TApp` tysubst)
  --     _   -> otherErr $ show $ "Expected" <+> pretty tysubst <+> "to be a Fix type"

  -- FoldApp
  -- check' (A fann (Prim Fold) `App` e2) (RecTy fty) = do
  --   root $ "[FoldApp]" <+> pretty e <+> "<=" <+> pretty ty
  --   branch $ check e2 (A tann $ fty `TApp` ty)

  -- UnfoldApp
  -- check' (A ufann (Prim Unfold) `App` e2) (ftor `TApp` unfty) = do
  --   root "[UnfoldApp]"
    -- branch $ check e2 $ unfty

  -- Sub
  check' _ _ = do
    ctx <- getCtx
    root $ "[Sub]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
    (aty, theta) <- branch $ synthesize e
    branch $ root $ "[Info] Synthesized" <+> pretty (aty, theta)
    atysubst <- substCtx theta aty
    btysubst <- substCtx theta ty
    withCtx (const theta) $ branch $ atysubst `subtypeOf` btysubst
  
  sanityCheck ty0 = do
    ctx <- getCtx
    _ <- wfContext ctx
    checkWfType ty0
  
  -- just introduce forall-quantified variables as existentials
  -- in the current context
  intros :: Type a Poly -> TypingM a (Type a Poly, TyCtx a)
  intros ty0@(A ann (Forall nm t)) = do
    root $ "[Intros]" <+> pretty ty0
    ahat <- freshName
    let t' = subst (A ann $ TExists ahat) nm t
    withCtx (\g -> g <+ Exists ahat) $ branch $ intros t'
  intros ty0 = do
    root $ "[Intros]" <+> pretty ty0
    ctx <- getCtx
    pure (ty0, ctx)

  -- Could be expressed as a fold, but this is a bit simpler methinks.
  -- Checks some clauses against an expected type.
  -- The marker is to make sure that the clauses can assign types to existentials
  -- that are in scope at the case-expr, but does not pollute the scope with new
  -- type variables that came into the context during the branch and body.
  checkCaseClauses :: Name -> Type a Poly -> [(Pat a, Expr a)] -> Type a Poly -> TypingM a ()
  checkCaseClauses markerName pty clauses expected = 
    case clauses of
      (pat, expr) : clauses' -> do
        ctx <- getCtx
        root $ "[CheckClause]" <+> pretty pat <+> "->" <+> pretty expr <+> "<=" <+> pretty expected <+> "in" <+> pretty ctx
        ctx' <- branch $ checkPat pat pty
        ctx'' <- withCtx (const ctx') $ branch $ check expr expected
        let nextCtx =  (dropTil (Marker markerName) ctx'') <+ Marker markerName
        withCtx (const nextCtx) $
            checkCaseClauses markerName pty clauses' expected
      [] -> pure ()

synthesize :: Expr a -> TypingM a (Type a Poly, TyCtx a)
synthesize expr@(A ann expr') = synthesize' expr' where
  -- Var
  synthesize' (Var nm) = do
    ctx <- getCtx
    fctx <- getFCtx
    case (nm `hasTypeInCtx` ctx <|> nm `hasTypeInFCtx` fctx) of
      Just ty -> do
        root $ "[Var]" <+> pretty expr <+> "=>" <+> pretty ty
        _ <- checkWfType ty
        pure (ty, ctx)

      Nothing -> root "[Var]" *> nameNotFound nm
  
  -- Anno
  synthesize' (Ann e ty) = do
    root $ "[Anno]" <+> pretty e <+> ":" <+> pretty ty
    ctx <- getCtx
    ty' <- substCtx ctx ty
    _ <- branch $ check e ty'
    (ty, ) <$> getCtx
  
  -- ->L=>
  synthesize' (Lam x Nothing e) = do
    root $ "[->L=>]" <+> pretty expr
    alpha <- freshName
    beta <- freshName
    let alphac = Exists alpha 
        betac  = Exists beta
        alphat = A ann $ TExists alpha 
        betat  = A ann $ TExists beta
    ctx' <- withCtx (\g -> g <+ alphac <+ betac <+ x `HasType` alphat) $
                    branch (check e betat)
    (delta, _, theta) <- splitCtx (x `HasType` alphat) ctx'
    pure (A ann $ alphat :->: betat, delta)
  
  -- ->ClockE
  synthesize' (App e1 (A _ (ClockVar kappa))) = do
    ctx <- getCtx
    root $ "[->ClockE]" <+> pretty expr <+> "in" <+> pretty ctx
    (ty1, theta) <- branch $ synthesize e1
    case ty1 of 
      A _ (Clock kappa' cty) -> do
        ctysubst <- substCtx theta cty
        pure (ctysubst, theta)
      _ -> otherErr $ show $ "Cannot apply a clock variable to an expression that is not clock-quantified at" <+> pretty expr

  -- ->UnfoldE=>
  synthesize' (A uann (Prim Unfold) `App` e2) = do
    root "[->UnfoldE=>]"
    (e2ty, theta) <- branch $ synthesize e2 
    e2ty' <- substCtx theta e2ty 
    case e2ty' of
      A ann2 (RecTy fty) -> pure (A ann2 $ fty `TApp` e2ty', theta)
      _                  -> otherErr $ show $ pretty e2ty' <+> "cannot be unfolded"

  -- -- ->FoldE
  synthesize' (Prim Fold) = do
    ctx <- getCtx
    root $ "[->FoldE=>]" <+> "in" <+> pretty ctx
    a1 <- freshName
    let a1t = A ann (TExists a1)
    let rt = A ann (RecTy a1t)
    pure (A ann $ (A ann $ a1t `TApp` rt) :->: rt, ctx <+ Exists a1)

  -- synthesize' (A uann (Prim Fold) `App` e2) = do
  --   root "[->FoldE=>]"
  --   (e2ty, theta) <- branch $ synthesize e2 
  --   e2ty' <- substCtx theta e2ty
  --   case e2ty' of 
  --     A ann2 (fty `TApp` ty) -> pure (ty, theta)
  --     _                      -> otherErr $ show $ pretty e2ty' <+> "cannot be folded"

  -- ->E
  synthesize' (e1 `App` e2) = do
    ctx <- getCtx
    root $ "[->E]" <+> pretty expr <+> "in" <+> pretty ctx
    (ty1, theta) <- branch $ synthesize e1
    ty1subst <- substCtx theta ty1
    withCtx (const theta) $ branch $ applysynth ty1subst e2 

  -- Prim=>
  synthesize' (Prim p) = do
    pt <- inferPrim p
    root $ "[Prim=>]" <+> pretty expr <+> "=>" <+> pretty pt
    ctx <- getCtx
    pure (A ann $ pt, ctx)

  -- Case=>
  synthesize' (Case e clauses) = do
    root $ "[Case=>]" <+> pretty e <+> enclose "[" "]" (cat $ map pretty clauses)
    cannotSynthesize expr
    -- (pty, delta) <- branch $ synthesize e
    -- cty <- withCtx (const delta) $ branch $ checkClauses (pty, Nothing) clauses
    -- ctx <- getCtx
    -- pure (cty, ctx)

  synthesize' _ = cannotSynthesize expr

inferPrim :: Prim -> TypingM a (Type' a Poly)
inferPrim p = TFree . UName <$> case p of
  Unit   -> pure "Unit"
  Nat _  -> pure "Nat"
  Fold   -> otherErr $ "Cannot infer type of primitive fold"
  Unfold -> otherErr $ "Cannot infer type of primitive unfold"

-- check that patterns type-check and return a new ctx extended with bound variables
checkPat :: Pat a -> Type a Poly -> TypingM a (TyCtx a)
checkPat pat@(A ann p) ty = do
  ctx <- getCtx
  root $ "[CheckPat]" <+> pretty pat <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
  dctx <- getDCtx
  case p of
    Bind nm -> pure $ ctx <+ nm `HasType` ty 

    Match nm pats -> case query nm dctx of
      Nothing    -> otherErr $ "Pattern " ++ show nm ++ " not found in context."
      Just destr -> do 
        ctx' <- branch $ checkPats pats destr ty
        -- traceM $ showW 80 $ pretty ctx'
        pure ctx'

-- Take a destructor and "existentialize it" - replace its bound type-variables
-- with fresh existentials
existentialize :: forall a. a -> Destr a -> TypingM a (TyCtx a, Destr a)
existentialize ann destr = do
  (nms, destr') <- foldrM folder ([], destr) (bound destr)
  ctx <- getCtx
  let ctx' = foldr (\n g -> g <+ Exists n) ctx nms
  pure (ctx', destr')
  where
    folder b (nms, d@(Destr {typ, args})) = do
      b' <- freshName
      let s = subst (A ann $ TExists b') b
      let ntyp = s typ
      let nargs = map s args
      pure $ (b' : nms, d {typ = ntyp, args = nargs})
  

-- in a context, check a list of patterns against a destructor and an expected type.
-- if it succeeds, it binds the names listed in the pattern match to the input context
checkPats :: [Pat a] -> Destr a -> Type a Poly -> TypingM a (TyCtx a)
checkPats pats d@(Destr {name, typ, args}) expected@(A ann _)
  | length pats /= length args = 
      otherErr $ show $ "Expected" <+> pretty (length args) 
             <+> "arguments to" <> pretty name <+> "but got" <+> pretty (length pats)
  -- | typ         =/%= expected    = 
  --     otherErr $ show $ "Pattern '" <> pretty name <> "' has type" <+> pretty typ 
  --            <+> "but expected" <+> pretty expected
  | otherwise                  = do
      (delta, Destr {typ = etyp, args = eargs}) <- existentialize ann d
      -- traceM $ show $ pretty name <> ":" <+> pretty typ <+> "with args" <+> pretty args
      ctx' <- withCtx (const delta) $ branch $ etyp `subtypeOf` expected
      -- traceM (show $ pretty ctx')
      foldlM folder ctx' $ zip pats eargs
      where 
        folder acc (p, t) = do 
          t' <- substCtx acc t
          withCtx (const acc) $ checkPat p t'
  
applysynth :: Type a Poly -> Expr a -> TypingM a (Type a Poly, TyCtx a)
applysynth ty@(A tann ty') e@(A eann e') = applysynth' ty' where
  -- ∀App
  applysynth' (Forall alpha aty) = do
    ctx <- getCtx
    root $ "[∀App]" <+> pretty ty <+> "•" <+> pretty e <+> "in" <+> pretty ctx
    -- fresh name to avoid clashes
    alpha' <- freshName
    let atysubst = subst (A tann $ TExists alpha') alpha aty
    withCtx (\g -> g <+ Exists alpha') $ branch $ applysynth atysubst e
  
  -- ^alpha App
  applysynth' (TExists alpha) = do
    root "̂[αApp]"
    ctx <- getCtx
    if Exists alpha `isInContext` ctx
      then do
        a1 <- freshName
        a2 <- freshName
        let a1toa2 = A tann $ A tann (TExists a1) :->: A tann (TExists a2)
        ctx' <- insertAt (Exists alpha) (mempty <+ Exists a2 <+ Exists a1 <+ alpha := a1toa2)
        delta <- branch $ check e (A tann $ TExists a1)
        pure (A tann $ TExists a2, delta)
      else
        nameNotFound alpha
  
  -- ->App
  applysynth' (aty :->: cty) = do
    ctx <- getCtx
    root $ "[->App]" <+> pretty ty <+> "in" <+> group (pretty ctx)
    delta <- branch $ check e aty
    pure (cty, delta)
  
  applysynth' (Clock _ _) = otherErr $ show $ "Expected" <+> pretty e <+> "to be a clock"
    
  
  applysynth' _ = root "[CannotAppSynthesize]" *> cannotAppSynthesize ty e

