{-|
Module      : CloFRP.Check
Description : Type-checking and inference algorithm for CloFRP.

Based on Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism 
by Joshua Dunfeld and Neel Krishnaswami
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

import GHC.TypeLits
import Data.Proxy (Proxy)
import Data.Foldable (foldlM, foldrM)
import Control.Monad.Writer (tell)
import Control.Applicative ((<|>))
import Control.Monad.Except (catchError, throwError)
import Control.Monad (filterM)
import GHC.Exts (toList, fromList)
import Data.Text.Prettyprint.Doc
import Data.List (find, genericLength)
import Data.Maybe (isJust, catMaybes)

import CloFRP.AST.Name
import qualified CloFRP.Check.Coverage as Coverage
import qualified CloFRP.AST.Helpers as H
import CloFRP.Context
import CloFRP.Annotated
import CloFRP.AST hiding (exists)
import CloFRP.Pretty
import CloFRP.Check.Destr (Destr)
import CloFRP.Check.Contexts
import CloFRP.Check.TypingM
import CloFRP.Check.Utils
import CloFRP.Check.Subtyping
import CloFRP.Check.Instantiation
import CloFRP.Check.Pat

import qualified CloFRP.Check.Destr as Destr


-- | For testing
runSubtypeOf0 :: PolyType a -> PolyType a -> TypingMRes a (LocalCtx a)
runSubtypeOf0 t1 t2 = runSubtypeOf initRead t1 t2

-- | For testing
runSubtypeOf :: TypingRead a -> PolyType a -> PolyType a -> TypingMRes a (LocalCtx a)
runSubtypeOf rd t1 t2 = runTypingM (t1 `subtypeOf` t2) rd initState

-- | Run a type-checking computation in an empty context
runCheck0 :: Expr a -> PolyType a -> TypingMRes a (LocalCtx a)
runCheck0 e t = runCheck initRead e t

-- | Run a type-checking computation in a given context
runCheck :: TypingRead a -> Expr a -> PolyType a -> TypingMRes a (LocalCtx a)
runCheck rd e t = runTypingM (check e t) rd initState

-- | Run a type-synthesizing computation in a given context
runSynth :: TypingRead a -> Expr a -> TypingMRes a (PolyType a, LocalCtx a)
runSynth rd e = runTypingM (synthesize e) rd initState

-- | Substitute a type using a context. As defined in the paper Θ[τ]. Will substitute
-- zero or more existential type variables for something "more-solved".
-- Proceeds by completely standard induction over the type, except for the TExists case,
-- Γ[α^ = τ'][α^] = Γ[τ'] which recurses back on the assigned type of α^,
-- which can be called a "simultaneous substitution"

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


-- | Query the kind of a name in the current context

-- | Insert another context (a list of ctx-elems) into the current context at a specific element.
-- It will replace the element with the new inserted context

-- | Get the kind of a type in the current context


-- | Check if a given context is well-formed

-- | Check if a type has kind * in a context
validType :: KindCtx a -> PolyType a -> TypingM a ()
validType kctx t = do
  k <- withKCtx (const kctx) $ kindOf t
  case k of
    Star -> pure ()
    _    -> otherErr $ show $ pretty t <+> "has kind" <+> pretty k
        <+> "but expected *"


-- | Assert that a type is functorial, namely that there is an instance of Functor for that type
assertFunctor :: PolyType a -> TypingM a ()
assertFunctor ty = findInstanceOf "Functor" ty >>= \case
  Just _ -> pure ()
  Nothing -> otherErr $ show $ "Cannot resolve functor instance of" <+> pretty ty

-- | Check that an expr has a type
check :: Expr a -> PolyType a -> TypingM a (LocalCtx a)
check e@(A eann e') ty@(A tann ty') = sanityCheck ty *> check' e' ty' where

  -- 1I
  check' (Prim Unit) (TFree "Unit") = getCtx
  check' (Prim (Integer _)) (TFree "Int") = getCtx

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
    delta'' <- withCtx (const $ delta' <+ Marker markerName) 
      $ branch $ checkCaseClauses markerName pty'' clauses tysubst
    pure delta''

  -- TickAbsI
  -- At the exam, I had a bug here with (const $ delta <+ c) because it was
  -- (\g -> g <+ c) which meant that we propagated the wrong context, leading to
  -- inferring existentials for clock variables always
  check' (TickAbs af k e2) (Later k' t2) = do
    rule "TickAbsI" (pretty e <+> "<=" <+> pretty ty)
    let kty = nameToType eann k
    delta <- branch $ k' `subtypeOf` kty
    kty' <- substCtx delta kty
    let c = (LamB, af) `HasType` kty'
    (theta, _, _) <- splitCtx c =<< withCtx (const $ delta <+ c) (branch $ check e2 t2)
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
  intros :: PolyType a -> TypingM a (PolyType a, LocalCtx a)
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
  checkCaseClauses :: Name -> PolyType a -> [(Pat a, Expr a)] -> PolyType a -> TypingM a (LocalCtx a)
  checkCaseClauses markerName pty clauses expected =
    case clauses of
      (pat, expr) : clauses' -> do
        rule "CheckClause" ("|" <+> pretty pat <+> "->" <+> pretty expr <+> "<=" <+> pretty expected)
        (expected', ctx') <- checkClause pty (pat, expr) expected
        let nextCtx =  (dropTil (Marker markerName) ctx') <+ Marker markerName
        pty' <- substCtx ctx' pty `decorateErr` (Other "[checkCaseClauses]")  -- more substCtx for (hopefully) better inference
        withCtx (const nextCtx) $
            checkCaseClauses markerName pty' clauses' expected'
      [] -> getCtx

  -- using substCtx alot improves inference. If the first clause infers that the pat is type P and
  -- body is type A, then subsequent patterns must also check against this more refined type.
  checkClause :: PolyType a -> (Pat a, Expr a) -> PolyType a -> TypingM a (PolyType a, LocalCtx a)
  checkClause pty (pat, expr) expected = do
    ctx' <- branch $ checkPat pat pty
    expected' <- substCtx ctx' expected `decorateErr` (Other "[checkClause.1]")
    ctx'' <- withCtx (const ctx') $ branch $ check expr expected'
    expected'' <- substCtx ctx'' expected' `decorateErr` (Other "[checkClause.2]")
    pure (expected'', ctx'')

-- | Synthesize a type A from an expression E, along with an output context
synthesize :: Expr a -> TypingM a (PolyType a, LocalCtx a)
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
    let tausubst = foldr (\(x', _k) acc -> subst (A ann $ TVar x') x' acc) tau unsolved
    let quanted = foldr (\(x', k) acc -> A ann $ Forall x' k acc) tausubst unsolved
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
    e1tys <- substCtx theta e1ty `decorateErr` (Other "[Let=>]")
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
    ety' <- substCtx ctx' ety `decorateErr` (Other "[TickAbs=>]")
    (delta, _, _) <- splitCtx c ctx'
    let lty = A ann $ Later kt ety'
    pure (lty, delta)

  -- TypeApp=>
  synthesize' (TypeApp ex arg) = do
    root $ "[TypeApp=>]" <+> pretty expr
    (exty, theta) <- branch $ synthesize ex
    extys <- substCtx theta exty `decorateErr` (Other "[TypeApp=>]")
    checkWfType arg
    -- _ <- asMonotypeTM arg
    k' <- kindOf arg
    case extys of
      A _ (Forall af k faty)
        | k' == k -> pure (subst arg af faty, theta)

      _           -> otherErr $ show $ pretty ex <+> "of type" <+> pretty exty <+> "cannot be applied to the type" <+> pretty arg <+> "of kind" <+> pretty k'

  synthesize' (BinOp "+" e1 e2) = do 
    delta <- check e1 (A ann $ TFree "Int")
    theta <- withCtx (const delta) $ check e2 (A ann $ TFree "Int")
    pure (A ann $ TFree "Int", theta)

  synthesize' (BinOp "<" e1 e2) = do 
    delta <- check e1 (A ann $ TFree "Int")
    theta <- withCtx (const delta) $ check e2 (A ann $ TFree "Int")
    pure (A ann $ TFree "Bool", theta)

  synthesize' _ = cannotSynthesize expr

-- | Infer the type of a primitive, along with an output context
inferPrim :: a -> Prim -> TypingM a (PolyType a, LocalCtx a)
inferPrim ann p = case p of
  Unit   -> (A ann (TFree $ UName "Unit"), ) <$> getCtx
  Integer _  -> (A ann (TFree $ UName "Int"), ) <$> getCtx
  Undefined -> (A ann $ Forall "a" Star (A ann $ TVar "a"), ) <$> getCtx

  -- The tick constant unifies with any clock variable?
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

  Fix -> do
    let ltr k = A ann . Later k
    let kappa = tv "k"
    let at = tv "a"
    let aq = fall "a" Star
    let kq = fall "k" ClockK
    ctx <- getCtx
    pure (kq . aq $ (ltr kappa at --> at) --> at, ctx)
  
  Input -> error "Input should never be present in the syntax"

  where
    infixr 9 -->
    x --> y = A ann (x :->: y)
    fall n k = A ann . Forall n k
    tv = A ann . TVar . UName
    tapp t1 = A ann . TApp t1


-- | Check that a pattern type-checks and return a new ctx extended with bound variables


-- | Synthesize the type of an application of a term of type A to expression e,
-- yielding a synthesized type C and an output context Δ
applysynth :: forall a. PolyType a -> Expr a -> TypingM a (PolyType a, LocalCtx a)
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
    rule "|>kApp<>" (pretty ty <+> "•" <+> pretty e)
    kappa <- fromEither $ extractKappa kappat
    ctx <- getCtx
    ctx `mustBeStableUnder` kappa
    pure (cty, ctx)

  -- |>κApp
  applysynth' (Later kappat cty) _ = do
    rule "|>kApp" (pretty ty <+> "•" <+> pretty e)
    k <- kindOf kappat
    if k /= ClockK
      then otherErr $ show $ pretty kappat <> "must have the kind of clocks"
      else (cty,) <$> branch (check e kappat)

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


foobar :: [Bool] -> ()
foobar xs =
  case xs of
    [] -> ()
    True:_y:_xs -> ()
    _x:_xs -> ()
{-
  -- solution be expanding patterns 

  #Example 1. unreachable
  case xm of
    | Nothing
    | Just MkUnit
    | Just x
  
  xm coveredBy [Nothing, Just MkUnit]
  |
  | split xm into destructors
  |
  v
  Nothing coveredBy [Nothing] -- discharge
  Just `a coveredBy [Just MkUnit, Just x]
  |
  | first pattern covers ideal, but there is more
  |
  v
  Just x unreachable!
  -------------------

  #Example 2. not exhaustive
  case xs of
    | Nil
    | Cons x Nil
  
  xs coveredBy [Nil, Cons x Nil]
  |
  | split xs into destructors
  v
  Nil coveredBy [Nil] -- discharge
  Cons `a `b coveredBy [Cons x Nil]
  |
  | `a matches x, but split `b to match Nil
  v
  Cons `a Nil coveredBy [Cons x Nil]
  Cons `a (Cons `b `c) coveredBy [Cons x Nil] <-- cant cover
  -------------------------------------------

  #Example 3. correct nested patterns
  case lst of
    | Nil -> ...
    | Cons True (Cons y xs) -> ...
    | Cons x xs -> ...
  
  lst coveredBy [Nil, Cons True (Cons y xs), Cons x xs]
  |
  | split lst in destructors
  v
  Nil coveredBy [Nil] -- discharge
  Cons `a `b coveredBy [Cons True (Cons y xs), Cons x xs]
  |
  | split on `a since x is not in constructor form
  v
  Cons True `b  coveredBy [Cons True (Cons y xs), Cons True xs]
  Cons False `b coveredBy [Cons False xs]
  |
  | split on `b since xs is not in constructor form
  | we could skip second split if we check that no pattern scrutinizes `b
  |
  v
  Cons True Nil           coveredBy [Cons True Nil] -- discharge
  Cons True (Cons `c `d)  coveredBy [Cons True (Cons `c `d)] -- discharge
  Cons False Nil          coveredBy [Cons False Nil] -- discharge
  Cons False (Cons `c `d) coveredBy [Cons False (Cons `c `d)] -- discharge

  #Example 4. Same as above, but narrowing scopes (won't work)
  
  lst coveredBy [Nil, Cons True (Cons y xs), Cons x xs]
  |
  | split lst in destructors
  v
  Nil coveredBy [Nil] -- discharge
  Cons `a `b coveredBy [Cons True (Cons y xs), Cons x xs]
  |
  | split and focus on `a since x is not in constructor form
  v
  True coveredBy [True, True] <-- will erroneously report an unreachable pattern!
  False coveredBy [False]
   
  # Example 5. unreachable
  case lst of
    | Nil
    | Cons x Nil
    | x
  
  lst coveredBy [Nil, Cons x Nil, x]
  |
  | split lst
  v
  Nil coveredBy [Nil, Nil] <-- unreachable
  Cons `a `b coveredBy [Cons x Nil, Cons `a `b]

  # questions:
  - Do we need to maintain the full patterns and expand, or can't we just
    recurse down into them based on position? Seems like we cant

  lst coveredBy [Nil, Cons x Nil, Cons x (Cons y xs)]
    refine lst -> Nil
      Nil coveredBy [Nil]
    refine lst -> Cons `a `b
      Cons `a `b coveredBy [Cons x Nil, Cons x (Cons y xs)]
        refine 

  # Pseudo code
  coveredBy ideal covering = do
    if ideal is a binding 
      then do
        let refinements = destructors of ideal's type
        foreach (Match nm subpatterns) in refinements do
          let covering' = all Match nm' _ in covering where nm == nm'
          if (null subpatterns) and (length covering' == 1)
            then discharge refinement case
            else do


  # Pseudo code
  coveredBy :: Pat a -> [Pat a] -> TypingM a ()
  coveredBy _ [] = not exhaustive!
  coveredBy (Bind nm) patterns = do
    idealpats <- lookupPats nm
    foreach ipat in idealpats
      coveredby ipat (filter matchIpat patterns)
  coveredBy (Match nm subpats) (pat : patterns) = do
    if null subpats
      then if null patterns
        then done!
      else (head patterns) is unreachable!
    else do
-}

-- data PatternType = PBind | PMatch

-- data CovPattern :: Symbol -> PatternType -> * where
--   CovBind :: String -> CovPattern s 'PBind
  -- CovMatch :: Proxy s -> [CovPattern s' pt] -> CovPattern s 'PMatch

-- coveredBy' :: Pat a -> [Pat a] -> TypingM a ()
-- coveredBy' = go Here
--   where
--     go _ ideal [] = notExhaustive ideal
--     go index ideal covering = do
--       branches <- refineIdealAt index ideal covering
--       traverse (traverseBranch index) branches
    
--     traverseBranch index (ideal, covering) =
--       case ideal of
--         A _ (Bind _) -> error "bind not expected"
--         A _ (Match nm subideals) -> 


-- data PatIndex = Here | Deeper Int PatIndex
--   deriving (Show, Eq)

-- getLeaf :: PatIndex -> Pat a -> Maybe Name
-- getLeaf Here p@(A _ (Bind nm)) = Just nm
-- getLeaf (Deeper offset i) (A _ (Match _ subps)) = do
--   branch <- atIndex offset subps
--   getLeaf i branch

-- modifyLeafAt :: (a -> Name -> Pat a) -> PatIndex -> Pat a -> Maybe (Pat a)
-- modifyLeafAt fn = go
--   where
--     go Here (A ann (Bind nm)) = Just (fn ann nm)
--     go (Deeper offset i) (A ann (Match nm subps)) = do
--       subp <- atIndex offset subps
--       subp' <- go i subp
--       pure (A ann (Match nm (replaceAt offset subp' subps)))
      

-- atIndex :: Int -> [a] -> Maybe a
-- atIndex 0 (x : _) = Just x
-- atIndex n (x : xs) 
--   | n > 0 = atIndex (n-1) xs
-- atIndex _ _ = Nothing

-- freshPatternsFromName :: Name -> TypingM a [Pat a]
-- freshPatternsFromName nm = do 
--   mty <- lookupTy nm <$> getCtx
--   case mty of 
--     Nothing -> nameNotFound nm
--     Just ty -> silentBranch $ getPatternsOfType ty

-- refineIdealAt :: PatIndex -> Pat a -> [Pat a] -> TypingM a [(Pat a, [Pat a])]
-- refineIdealAt index ideal covering = do
--   nm <- getLeafLifted index ideal
--   refinements <- freshPatternsFromName nm
--   pure (map refineCovering refinements)
--   where
--     refineCovering refinement =
--       (refinement, substPatsByIndex index refinement covering)
    
--     getLeafLifted index pat =
--       case getLeaf index pat of
--         Nothing -> otherErr $ "Cannot get pattern leaf at index " 
--                    ++ show index ++ " in pattern" ++ pps pat
--         Just pat' -> pure pat'

-- substPatsByIndex :: PatIndex -> Pat a -> [Pat a] -> [Pat a]
-- substPatsByIndex index refined covering = 
--   map (overCovering index) covering
--   where
--     overCovering i coveringPat =
--       maybe coveringPat id (modifyLeafAt (\_ann _nm -> refined) i coveringPat)


-- getPatternsOfType :: PolyType a -> TypingM a [Pat a]
-- getPatternsOfType qtype@(A ann _) = do
--   rule "GetPatternsOfType" (pretty qtype)
--   destrs <- branch $ getDestrsOfType qtype
--   traverse (destrToPat ann) destrs

-- destrToPat :: a -> Destr a -> TypingM a (Pat a)
-- destrToPat ann destr = do
--   let name = Destr.name destr
--   let args = Destr.args destr
--   subvars <- traverse (\_ -> A ann . Bind <$> freshName) args
--   pure (A ann (Match name subvars))



-- replaceAt :: Int -> a -> [a] -> [a]
-- replaceAt i rep xs =
--   zipWith (\j x -> if i == j then rep else x) [0..] xs

-- coveredBy :: Pat a -> [Pat a] -> TypingM a ()
-- coveredBy idealPat coveringPats =
--   case (idealPat, coveringPats) of
--     (_, []) -> coverRule "UncoveredCases" >> uncoveredCases idealPat

--     (_, A _ (Bind _) : ps) ->
--       case ps of
--         [] -> coverRule "Bind" >> pure ()
--         (p : _) -> coverRule "UnreachableCases" >> unreachableCases p

--     (A _ (Match nm1 []), p@(A _ (Match nm2 [])) : ps) | nm1 == nm2 -> 
--       case ps of
--         [] -> coverRule "Bind" >> pure ()
--         (p : _) -> coverRule "UnreachableCases" >> unreachableCases p

--     (A _ (Bind bnm), ps@(A _ (Match _mnm _mpts) : _)) -> do
--       mty <- lookupTy bnm <$> getCtx
--       case mty of 
--         Nothing -> otherErr $ show $ pretty bnm <+> "is not bound in local context"
--         Just ty -> do
--           coverRule "Split"
--           idealPats <- silentBranch $ getPatternsOfType ty
--           rule "GetPatternsOfType.Info" (pretty idealPats)
--           if null idealPats 
--             then error $ show $ "FATAL: empty type" <+> pretty ty <+> "encountered"
--             else do
--               let continue ip = do
--                     delta <- branch $ checkPat ip ty
--                     withCtx (const delta) $ branch $ coveredBy ip (matchesIdeal ip ps)
--               traverse continue idealPats
--               pure ()

--     (A matchAnn (Match nm1 idealps), A _ (Match nm2 nestedps) : ps)
--       | nm1 /= nm2 ->
--         coveredBy idealPat ps
--         -- error $ "todo: cannot match pattern " ++ pps nm1 ++ " with " ++ pps nm2
--       | length idealps /= length nestedps ->
--         error $ "FATAL: expected " ++ show (length idealps) ++ " sub-patterns but got " 
--         ++ show (length nestedps)
--       | otherwise -> do
--         coverRule "Nest"
--         let matchingps = [ ps' | A _ (Match nm1' ps') <- coveringPats, nm1 == nm1' ]
--         let catcher index = \case
--               (UncoveredCases newpat, _) -> uncoveredCases (updateIdeal index newpat)
--               (UnreachableCases newpat, _) -> unreachableCases (updateIdeal index newpat)
--               err -> throwError err
--         let zipper = \index ip -> 
--               (branch $ coveredBy ip (map (!! index) matchingps)) `catchError` catcher index
--         _ <- sequence $ zipWith zipper [0..] idealps 
--         pure ()
--         where
--           updateIdeal index newpat =
--             let newIdealPs = zipWith (\i p -> if i == index then newpat else p) [0..] idealps
--             in  A matchAnn (Match nm1 newIdealPs)
--   where
--     coverRule sub = 
--       rule ("CoveredBy." <> sub) (pretty idealPat <> indent 2 (line <> pretty coveringPats))

--     matchesIdeal (A _ ideal) pats =
--       case ideal of
--         Bind _ -> pats
--         Match nm _ -> 
--           filter (
--             \case 
--               A _ (Bind _) -> True
--               A _ (Match nm' _) -> nm' == nm
--           ) pats

      

-- getDestrsOfType :: PolyType a -> TypingM a [Destr a]
-- getDestrsOfType qtype@(A ann _) = do
--   destrCtx <- getDCtx
--   let destrs = map snd $ toList destrCtx
--   filterM onlySubtypes destrs
--   where
--     onlySubtypes destr = do
--       (delta, edestr) <- existentialize ann destr
--       withCtx (const delta) $ Destr.typ edestr `isSubtypeOf` qtype

