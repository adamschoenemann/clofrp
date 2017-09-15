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

module CloTT.Check.Poly where

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.AST.Parsed hiding (exists)
import Control.Monad.RWS.Strict hiding ((<>))
import Control.Monad.Except
import Control.Monad.State
import Data.List (break, intercalate, find)
import Control.Monad (foldM)
import Debug.Trace
import CloTT.Pretty
import Data.Maybe (isJust)
import Data.String (fromString)
import Data.Text.Prettyprint.Doc

data CtxElem a
  = Uni Name -- ^ Universal
  | Exists Name -- ^ Existential
  | Name `HasType` Type a Poly -- ^ x : A
  | Name := Type a Mono -- ^ a = t
  | Marker Name -- ^ |>a
  deriving Eq

instance Unann (CtxElem a) (CtxElem ()) where
  unann el = 
    case el of
      Uni nm          -> Uni nm
      Exists nm       -> Exists nm
      nm `HasType` ty -> nm `HasType` unann ty
      nm := ty        -> nm := unann ty
      Marker nm       -> Marker nm

instance Show (CtxElem a) where
  show = \case
    Uni nm          -> show nm
    Exists nm       -> "^" ++ show nm
    nm `HasType` ty -> show nm ++ " : " ++ show (unannT ty)
    nm := ty        -> show nm ++ " = " ++ show (unannT ty)
    Marker nm       -> "▷" ++ show nm

instance Pretty (CtxElem a) where
  pretty = \case
    Uni nm          -> pretty nm
    Exists nm       -> "^" <> pretty nm
    nm `HasType` ty -> pretty nm <> " : " <> pretty (unann ty)
    nm := ty        -> "^" <> pretty nm <> " = " <> pretty (unann ty)
    Marker nm       -> "▷" <> pretty nm


exists :: Name -> CtxElem a
exists = Exists

marker :: Name -> CtxElem a
marker = Marker

uni :: Name -> CtxElem a
uni = Uni

newtype TyCtx a = Gamma { unGamma :: [CtxElem a] }
  deriving (Eq)

instance Show (TyCtx a) where
  show gamma = "\n" ++ pps gamma 

instance Pretty (TyCtx a) where
  pretty (Gamma xs) = encloseSep "[" "]" ", " $ map pretty $ reverse xs

instance Unann (TyCtx a) (TyCtx ()) where
  unann (Gamma xs) = Gamma $ map unann xs

emptyCtx :: TyCtx a
emptyCtx = Gamma []

-- Lists are left-prepend but contexts are right-append
-- It doesn't matter, so we just pretend that we right-append stuff,
-- yet put it at the head 
infixl 5 <+
(<+) :: TyCtx a -> CtxElem a -> TyCtx a
Gamma xs <+ x = Gamma (x : xs)

infixl 4 <++
(<++) :: TyCtx a -> TyCtx a -> TyCtx a
Gamma xs <++ Gamma ys = Gamma (ys ++ xs)

isInContext :: CtxElem a -> TyCtx a -> Bool
isInContext el (Gamma xs) = isJust $ find (\x -> unann el == unann x) xs

-- A type is wellformed
-- TODO: Deal with free types
isWfTypeIn' :: Type a Poly -> TyCtx a -> Bool
isWfTypeIn' (A _ ty) ctx =
  case ty of
    -- UvarWF
    TFree x -> isJust $ ctxFind (freePred x) ctx
    -- EvarWF and SolvedEvarWF
    TExists alpha -> isJust $ ctxFind (expred $ alpha) ctx
    -- ArrowWF
    t1 :->: t2 -> isWfTypeIn' t1 ctx && isWfTypeIn' t2 ctx
    -- ForallWF
    Forall x t -> isWfTypeIn' t (ctx <+ Uni x)
    -- TAppWF. TODO: Use kind-ctx to make sure kinds are correct
    TApp t1 t2 -> isWfTypeIn' t1 ctx && isWfTypeIn' t2 ctx
  where 
    expred alpha = \case
      Exists alpha' -> alpha == alpha'
      alpha' := _   -> alpha == alpha' 
      _         -> False

    freePred x = \case
      Uni x' -> x == x'
      _      -> False


findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap fn = foldr fun Nothing where
  fun x acc = 
    case fn x of
      Just x' -> Just x'
      Nothing -> acc

ctxFind :: (CtxElem a -> Bool) -> TyCtx a -> Maybe (CtxElem a)
ctxFind p (Gamma xs) = find p xs

findAssigned :: Name -> TyCtx a -> Maybe (Type a Mono)
findAssigned nm (Gamma xs) = findMap fn xs >>= asMonotype where
  fn (nm' := ty) | nm == nm' = pure ty
  fn _                      = Nothing

hasTypeIn :: Name -> TyCtx a -> Maybe (Type a Poly)
hasTypeIn nm (Gamma xs) = findMap fn xs where
  fn (nm' `HasType` ty) | nm == nm' = pure ty
  fn _                             = Nothing

branch :: TypingM a r -> TypingM a r
branch comp = do
  i <- gets level
  modify $ \s -> s { level = i + 1 }
  r <- comp
  modify $ \s -> s { level = i }
  pure r

root :: String -> TypingM a ()
root x = gets level >>= \l -> tell [(l,x)]

data TypingState   = 
  TS { names :: Integer -- |Just an integer for generating names
     , level :: Integer
     }

type TypingRead a  = TyCtx a
type TypingWrite a = [(Integer, String)]
type TypingErr a = (TyExcept a, TyCtx a)

showTree :: TypingWrite a -> String
showTree [] = ""
showTree ((i,s):xs) = indented  ++ showTree xs where
  indented = unlines $ map (replicate (fromIntegral (i * 4)) ' ' ++) $ lines s

data TyExcept a
  = Type a Poly `CannotSubtype` Type a Poly
  | Name `OccursIn` Type a Poly
  | NameNotFound Name
  | CannotSplit (CtxElem a) (TyCtx a)
  | CannotSynthesize (Expr a)
  | CannotAppSynthesize (Type a Poly) (Expr a)
  | Other String
  deriving (Show, Eq)

instance Unann (TyExcept a) (TyExcept ()) where
  unann = \case
    ty `CannotSubtype` ty'   -> unann ty `CannotSubtype` unann ty'
    nm `OccursIn` ty         -> nm `OccursIn` unann ty
    NameNotFound x           -> NameNotFound x
    CannotSplit el ctx       -> CannotSplit (unann el) (unann ctx)
    CannotSynthesize e       -> CannotSynthesize (unann e)
    CannotAppSynthesize ty e -> CannotAppSynthesize (unann ty) (unann e)
    Other s                  -> Other s

instance Pretty (TyExcept a) where
  pretty = \case
    ty `CannotSubtype` ty'   -> pretty ty <+> "cannot subtype" <+> pretty ty'
    nm `OccursIn` ty         -> pretty nm <+> "occurs in" <+> pretty ty
    NameNotFound x           -> "Cannot find name" <+> pretty x
    CannotSplit el ctx       -> "Cannot split" <+> pretty ctx <+> "at" <+> pretty el
    CannotSynthesize e       -> "Cannot synthesize" <+> pretty e
    CannotAppSynthesize ty e -> "Cannot app_synthesize" <+> pretty ty <+> "•" <+> pretty e
    Other s                  -> "Other error:" <+> fromString s

tyExcept :: TyExcept a -> TypingM a r
tyExcept err = do 
  ctx <- getCtx 
  throwError (err, ctx)

cannotSubtype :: Type a Poly -> Type a Poly -> TypingM a r
cannotSubtype t1 t2 = tyExcept $ CannotSubtype t1 t2

cannotSynthesize :: Expr a -> TypingM a r
cannotSynthesize e = tyExcept $ CannotSynthesize e

cannotAppSynthesize :: Type a Poly -> Expr a -> TypingM a r
cannotAppSynthesize t e = tyExcept $ CannotAppSynthesize t e

occursIn :: Name -> Type a Poly -> TypingM a r
occursIn nm t = tyExcept $ OccursIn nm t

nameNotFound :: Name -> TypingM a r
nameNotFound nm = tyExcept $ NameNotFound nm

cannotSplit :: CtxElem a -> TyCtx a -> TypingM a r
cannotSplit el ctx = tyExcept $ CannotSplit el ctx

otherErr :: String -> TypingM a r
otherErr s = tyExcept $ Other s

newtype TypingM a r = Typ { unTypingM :: ExceptT (TypingErr a) (RWS (TypingRead a) (TypingWrite a) TypingState) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError (TypingErr a)
           , MonadState TypingState
           , MonadWriter (TypingWrite a)
           , MonadReader (TypingRead a)
           )

type TypingMRes a r = (Either (TypingErr a) r, TypingState, TypingWrite a)

runTypingM :: TypingM a r -> TypingRead a -> TypingState -> TypingMRes a r
runTypingM tm r s = runRWS (runExceptT (unTypingM tm)) r s

getCtx :: TypingM a (TyCtx a)
getCtx = ask

freshName :: TypingM a Name
freshName = do 
  i <- gets names
  modify $ \s -> s {names = names s + 1}
  pure $ MName i

initState :: TypingState
initState = TS 0 0

runTypingM0 :: TypingM a r -> TypingRead a -> TypingMRes a r
runTypingM0 tm r = runTypingM tm r initState

runSubtypeOf0 :: Type a 'Poly -> Type a 'Poly -> TypingMRes a (TyCtx a)
runSubtypeOf0 t1 t2 = runSubtypeOf emptyCtx t1 t2

runSubtypeOf :: TyCtx a -> Type a 'Poly -> Type a 'Poly -> TypingMRes a (TyCtx a)
runSubtypeOf ctx t1 t2 = runTypingM (t1 `subtypeOf` t2) ctx initState

runCheck0 :: Expr a -> Type a 'Poly -> TypingMRes a (TyCtx a)
runCheck0 e t = runCheck emptyCtx e t

runCheck :: TyCtx a -> Expr a -> Type a 'Poly -> TypingMRes a (TyCtx a)
runCheck ctx e t = runTypingM (check e t) ctx initState


substCtx' :: TyCtx a -> Type a Poly -> Either Name (Type a Poly)
substCtx' ctx (A a ty) = 
  case ty of
    TFree x -> pure $ A a $ TFree x
    TExists x -> 
      case findAssigned x ctx of
        Just tau -> pure $ asPolytype tau
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

substCtx :: TyCtx a -> Type a Poly -> TypingM a (Type a Poly)
substCtx ctx ty = 
  case substCtx' ctx ty of
    Left x -> otherErr $ "existential " ++ show x ++ " not in context during substitution"
    Right ctx' -> pure ctx'

-- | drop until an element `el` is encountered in the context. Also drops `el`
dropTil :: CtxElem a -> TyCtx a -> TyCtx a
dropTil el (Gamma xs) = Gamma $ tl $ dropWhile ((unann el /=) . unann) xs where
  tl []     = []
  tl (_:ys) = ys

-- again, since contexts are "reversed" notationally, this does not yield 
-- we switch ys and zs in the definition
splitCtx' :: CtxElem a -> TyCtx a -> Maybe (TyCtx a, CtxElem a, TyCtx a)
splitCtx' el ctx@(Gamma xs) =
  case break ((unann el ==) . unann) xs of
    (_, [])    -> Nothing
    (ys, z:zs) -> pure (Gamma zs, z, Gamma ys)

splitCtx :: CtxElem a -> TyCtx a -> TypingM a (TyCtx a, CtxElem a, TyCtx a)
splitCtx el ctx =
  case splitCtx' el ctx of
    Nothing -> root "splitCtx" *> cannotSplit el ctx
    Just x  -> pure x

subst :: Type a Poly -> Name -> Type a Poly -> Type a Poly
subst x forY (A a inTy) = 
  case inTy of
    TFree y     | y == forY  -> x
                | otherwise -> A a $ TFree y

    TExists y   | y == forY  -> x
                | otherwise -> A a $ TExists y

    Forall y t  | y == forY  -> A a $ Forall y t 
                | otherwise -> A a $ Forall y (subst x forY t)

    t1 `TApp` t2 -> A a $ subst x forY t1 `TApp` subst x forY t2
    
    t1 :->: t2 -> A a $ subst x forY t1 :->: subst x forY t2
    

-- | Check if an elem alpha comes before beta in a context
before' :: CtxElem a -> CtxElem a -> TyCtx a -> Bool
before' alpha beta (Gamma ctx) = (beta `comesBefore` alpha) ctx False False where
  comesBefore x y [] xr yr = yr
  comesBefore x y (a:as) False False
    | x =%= a     = comesBefore x y as True False
    | y =%= a     = False
    | otherwise = comesBefore x y as False False
  comesBefore x y (a:as) True False
    | x =%= a = False
    | y =%= a = True
    | otherwise = comesBefore x y as True False
  comesBefore _ _ _ _ _ = False

before :: CtxElem a -> CtxElem a -> TypingM a Bool
before alpha beta = before' alpha beta <$> getCtx

assign' :: Name -> Type a Mono -> TyCtx a -> Maybe (TyCtx a)
assign' nm ty (Gamma ctx) = 
  case foldr fn ([], False) ctx of
    (_, False) -> Nothing
    (xs, True) -> Just (Gamma xs)
  where
    fn (Exists nm') (xs, _) | nm == nm' = (nm := ty : xs, True)
    fn x (xs, b)                       = (x : xs, b)

assign :: Name -> Type a Mono -> TypingM a (TyCtx a)
assign nm ty = do
  ctx <- getCtx
  case assign' nm ty ctx of
    Nothing  -> root "assign" *> nameNotFound nm
    Just ctx' -> pure ctx'

insertAt' :: CtxElem a -> TyCtx a -> TyCtx a -> Maybe (TyCtx a)
insertAt' at insertee into = do
  (l, _, r) <- splitCtx' at into
  pure $ l <++ insertee <++ r

insertAt :: CtxElem a -> TyCtx a -> TypingM a (TyCtx a)
insertAt at insertee = do
  ctx <- getCtx
  case insertAt' at insertee ctx of
    Nothing   -> otherErr $ "Cannot insert into context " ++ show ctx ++ " at " ++ show at
    Just ctx' -> pure ctx'

-- Under input context Γ, instantiate α^ such that α^ <: A, with output context ∆
instL :: Name -> Type a Poly -> TypingM a (TyCtx a)
-- InstLSolve
instL ahat (asMonotype -> Just mty) = do
  ctx <- getCtx
  root $ "[InstLSolve] " ++ pps ahat ++ " = " ++ pps mty ++ " in " ++ pps ctx
  (gam, _, gam') <- splitCtx (Exists ahat) =<< getCtx
  pure (gam <+ ahat := mty <++ gam')
instL ahat (A a ty) = 
  case ty of
    -- InstLReach
    TExists bhat -> do
      root $ "InstLReach"
      Exists ahat `before` Exists bhat >>= \case
        True -> assign bhat (A a $ TExists ahat)
        False -> otherErr $ "InstLReach"

    -- InstLArr
    t1 :->: t2 -> do
      root $ "InstLArr"
      af1 <- freshName
      af2 <- freshName
      let ahat1 = exists af1
      let ahat2 = exists af2
      let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
      omega <- local (\g -> g <+ ahat1 <+ ahat2 <+ ahat := arr) $ branch (t1 `instR` af1)
      substed <- substCtx omega t2
      r <- local (const omega) $ branch (af2 `instL` substed)
      pure r
    
    -- InstLAllR
    Forall beta bty -> do
      root $ "InstLAllR"
      ctx' <- local (\g -> g <+ uni beta) $ branch (ahat `instL` bty)
      (delta, _, delta') <- splitCtx (uni beta) ctx'
      pure delta
    
    _ -> otherErr $ show (unannT' ty) ++ " not expected in instL"

instR :: Type a Poly -> Name -> TypingM a (TyCtx a)
-- InstRSolve
instR (asMonotype -> Just mty) ahat = do
  root $ "[InstRSolve] " ++ pps mty ++ " =<: " ++ pps ahat
  (gam, _, gam') <- splitCtx (Exists ahat) =<< getCtx
  pure (gam <+ ahat := mty <++ gam')
instR (A a ty) ahat = 
  case ty of
    -- InstRReach
    TExists bhat -> do 
      root $ "InstRReach"
      Exists ahat `before` Exists bhat >>= \case
        True -> assign bhat (A a $ TExists ahat)
        False -> otherErr $ "InstRReach"

    -- InstRArr
    t1 :->: t2 -> do
      root $ "InstRArr"
      af1 <- freshName
      af2 <- freshName
      let ahat1 = exists af1
      let ahat2 = exists af2
      let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
      omega <- local (\g -> g <+ ahat1 <+ ahat2 <+ ahat := arr) $ branch (af1 `instL` t1)
      substed <- substCtx omega t2
      r <- local (const omega) $ branch (substed `instR` af2)
      pure r
    
    -- InstRAllL
    Forall beta bty -> do
      root $ "InstRAllL"
      let substedB = subst (A a $ TExists beta) beta bty
      ctx' <- local (\g -> g <+ marker beta <+ exists beta) $ branch (substedB `instR` ahat)
      (delta, _, delta') <- splitCtx (marker beta) ctx'
      pure delta
    
    _ -> otherErr $ show (unannT' ty) ++ " not expected in instR"

-- Under input context Γ, type A is a subtype of B, with output context ∆
-- A is a subtype of B iff A is more polymorphic than B
-- TODO: Consider how to avoid name capture (alpha renaming probably)
subtypeOf :: Type a Poly -> Type a Poly -> TypingM a (TyCtx a)
subtypeOf ty1@(A ann1 typ1) ty2@(A ann2 typ2) = subtypeOf' typ1 typ2 where
  -- <:Var
  subtypeOf' (TFree x) (TFree x')
        | x == x'    = root (pps ty1 ++ " <: " ++ pps ty2 ++ " [<:Var]") *> getCtx
        | otherwise = root (pps ty1 ++ " <: " ++ pps ty2 ++ " [<:Var]") *> cannotSubtype ty1 ty2
  
  -- <:Exvar
  subtypeOf' (TExists a) (TExists a') =
    root "<:Exvar" *> case () of
      _ | a == a' -> do 
          ctx <- getCtx
          if Exists a `isInContext` ctx
            then pure ctx
            else branch $ nameNotFound a
        | otherwise -> branch $ cannotSubtype ty1 ty2

  -- <:->
  subtypeOf' (a1 :->: a2) (b1 :->: b2) = do
    root $ "[<:->] " ++ pps ty1 ++ " <: " ++ pps ty2
    ctx' <- branch (b1 `subtypeOf` a1)
    a2' <- substCtx ctx' a2
    b2' <- substCtx ctx' b2
    r <- local (const ctx') $ branch (a2' `subtypeOf` b2')
    pure r

  -- <:\/R
  subtypeOf' t1 (Forall a (A _ t2)) = do
    root "<:\\/R"
    ctx' <- local (\g -> g <+ uni a) $ branch (t1 `subtypeOf'` t2)
    pure $ dropTil (uni a) ctx'

  -- <:\/L
  subtypeOf' (Forall nm (A at1 t1)) t2 = do
    root "<:\\/L"
    let A _ t1' = subst (A at1 $ TExists nm) nm (A at1 t1)
    ctx' <- local (\g -> g <+ marker nm <+ exists nm) $ branch (t1' `subtypeOf'` t2)
    pure $ dropTil (marker nm) ctx'
  
  -- <:InstantiateL
  subtypeOf' (TExists ahat) _
    | ahat `inFreeVars` ty2 = root "[InstantiateL] OccursError!" *> occursIn ahat ty2
    | otherwise = do 
      ctx <- getCtx
      if (A ann1 $ TExists ahat) `isWfTypeIn'` ctx 
        then do 
          root $ "[InstantiateL] " ++ pps ahat ++ " :<= " ++ pps ty2 ++ " in " ++ pps ctx
          r <- branch (ahat `instL` ty2)
          pure r
        else do
          root $ "[InstantiateL] " ++ pps ahat ++ " :<= " ++ pps ty2 ++ " |- NameNotFound "
                 ++ pps ahat ++ " in " ++ pps ctx
          nameNotFound ahat

  -- <:InstantiateR
  subtypeOf' _ (TExists ahat)
    | ahat `inFreeVars` ty1 = root "InstantiateR" *> occursIn ahat ty1
    | otherwise = do 
      ctx <- getCtx
      if (A ann2 $ TExists ahat) `isWfTypeIn'` ctx 
        then do 
          root $ "[InstantiateR] " ++ pps ty1 ++ " =<: " ++ pps ahat
          r <- branch (ty1 `instR` ahat)
          pure r
        else do
          root $ "[InstantiateR] " ++ pps ty1 ++ " =<: " ++ pps ahat ++ " |- NameNotFound "
                 ++ pps ahat ++ " in " ++ pps ctx
          nameNotFound ahat
  
  subtypeOf' t1 t2 = cannotSubtype ty1 ty2

check :: Expr a -> Type a Poly -> TypingM a (TyCtx a)
check e@(A eann e') ty@(A tann ty') = check' e' ty' where
  -- 1I (PrimI)
  check' (Prim p) _ 
    | ty' =%= inferPrim p = root "[PrimI]" *> ask
  -- check' (Prim p) _ = do
  --   ctx <- getCtx
  --   root $ "[PrimI] " ++ pps p ++ " <= " ++ pps ty ++ " in " ++ pps ctx
  --   let pty = A eann $ inferPrim p
  --   _ <- branch $ ty `subtypeOf` pty
  --   getCtx
  
  -- ∀I
  check' _ (Forall alpha aty) = do
    root "∀I"
    (delta, _, _) <- splitCtx (Exists alpha) =<< local (\g -> g <+ Exists alpha) (branch $ check e aty)
    pure delta
  
  -- ->I
  check' (Lam x Nothing e2) (aty :->: bty) = do
    root "->I"
    let c = x `HasType` aty
    (delta, _, _) <- splitCtx c =<< local (\g -> g <+ c) (branch $ check e2 bty)
    pure delta

  -- Sub
  check' _ _ = do
    root "Sub"
    (aty, theta) <- branch $ synthesize e
    atysubst <- substCtx theta aty
    -- traceM $ "atysubst: " ++ pps atysubst
    btysubst <- substCtx theta ty
    local (const theta) $ branch $ atysubst `subtypeOf` btysubst



synthesize :: Expr a -> TypingM a (Type a Poly, TyCtx a)
synthesize expr@(A ann expr') = synthesize' expr' where
  -- Var
  synthesize' (Var nm) = do
    root "Var"
    ctx <- getCtx
    case nm `hasTypeIn` ctx of
      Just ty -> pure (ty, ctx)
      Nothing -> nameNotFound nm
  
  -- Anno
  synthesize' (Ann e ty) = do
    root "Anno"
    _ <- branch $ check e ty
    (ty, ) <$> getCtx
  
  -- ->L=>
  synthesize' (Lam x Nothing e) = do
    root "->L=>"
    alpha <- freshName
    beta <- freshName
    let alphac = Exists alpha 
        betac  = Exists beta
        alphat = A ann $ TExists alpha 
        betat  = A ann $ TExists beta
    ctx' <- (\g -> g <+ alphac <+ betac <+ x `HasType` alphat) <$> getCtx
    (delta, _, theta) <- splitCtx (x `HasType` alphat) =<< (branch $ check e betat)
    pure (A ann $ alphat :->: betat, delta)
  
  -- ->E
  synthesize' (App e1 e2) = do
    root "->E"
    (ty1, theta) <- branch $ synthesize e1
    ty1subst <- substCtx theta ty1
    local (const theta) $ branch $ applysynth ty1subst e2 

  -- Prim=>
  synthesize' (Prim p) = root "Prim=>" *> ((A ann $ inferPrim p, ) <$> getCtx)

  synthesize' _ = cannotSynthesize expr

inferPrim :: Prim -> Type' a Poly
inferPrim p = TFree $ UName $ case p of
  Unit   -> "Unit"
  Bool _ -> "Bool"
  Nat _  -> "Nat"

applysynth :: Type a Poly -> Expr a -> TypingM a (Type a Poly, TyCtx a)
applysynth ty@(A tann ty') e@(A eann e') = applysynth' ty' where
  -- ∀App
  applysynth' (Forall alpha aty) = do
    root $ "∀App " ++ pps ty
    -- fresh name to avoid clashes
    alpha' <- freshName
    let atysubst = subst (A tann $ TExists alpha') alpha aty
    local (\g -> g <+ Exists alpha') $ branch $ applysynth atysubst e
  
  -- ^alpha App
  applysynth' (TExists alpha) = do
    root "̂αApp"
    ctx <- getCtx
    if Exists alpha `isInContext` ctx
      then do
        a1 <- freshName
        a2 <- freshName
        let a1toa2 = A tann $ A tann (TExists a1) :->: A tann (TExists a2)
        ctx' <- insertAt (Exists alpha) (emptyCtx <+ Exists a2 <+ Exists a1 <+ alpha := a1toa2)
        delta <- branch $ check e (A tann $ TExists a1)
        pure (A tann $ TExists a2, delta)
      else
        nameNotFound alpha
  
  -- ->App
  applysynth' (aty :->: cty) = do
    ctx <- getCtx
    root $ showW 80 $ "[->App]" <+> pretty ty <+> "in" <+> group (pretty ctx)
    delta <- branch $ check e aty
    pure (cty, delta)
  
  applysynth' _ = cannotAppSynthesize ty e

