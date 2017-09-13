{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module CloTT.Check.Poly where

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.AST.Parsed hiding (exists)
import Control.Monad.RWS.Strict
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.State
import Data.List (break, intercalate, find)
import Control.Monad (foldM)
import Debug.Trace

data CtxElem a
  = Uni Name -- ^ Universal
  | Exists Name -- ^ Existential
  | Name `HasType` Type a Poly -- ^ x : A
  | Name := Type a Mono -- ^ a = t
  | Marker Name -- ^ |>a
  deriving Eq

instance Show (CtxElem a) where
  show = \case
    Uni nm          -> show nm
    Exists nm       -> "^" ++ show nm
    nm `HasType` ty -> show nm ++ " : " ++ show (unannT ty)
    nm := ty        -> show nm ++ " = " ++ show (unannT ty)
    Marker nm       -> "▷" ++ show nm

exists :: Name -> CtxElem a
exists = Exists

marker :: Name -> CtxElem a
marker = Marker

uni :: Name -> CtxElem a
uni = Uni

newtype TyCtx a = Gamma { unGamma :: [CtxElem a] }
  deriving (Eq)

instance Show (TyCtx a) where
  show (Gamma xs) = show $ reverse xs

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

-- FIXME: We don't want to depend on (Eq a) since we do not consider the annotations
-- for equality. But I don't want to override the default Eq, because it is good
-- for testing purposes
isInContext :: Eq a => CtxElem a -> TyCtx a -> Bool
isInContext el (Gamma xs) = el `elem` xs

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap fn = foldr fun Nothing where
  fun x acc = 
    case fn x of
      Just x' -> Just x'
      Nothing -> acc

findAssigned :: Name -> TyCtx a -> Maybe (Type a Mono)
findAssigned nm (Gamma xs) = findMap fn xs >>= asMonotype where
  fn (nm' := ty) | nm == nm' = pure ty
  fn _                      = Nothing

data BuildTree a
  = Empty
  | Root a [BuildTree a]
  | Extend [BuildTree a]

branch :: MonadWriter (BuildTree a) m => m r -> m r
branch = censor (Extend . (:[]))

root :: MonadWriter (BuildTree a) m => a -> m ()
root x = tell (Root x [])

extend :: MonadWriter (BuildTree a) m => a -> m ()
extend x = tell (Extend [Root x []])

instance Monoid (BuildTree a) where
  mempty = Empty
  mappend Empty y = y
  mappend x Empty = x
  mappend (Extend xs) (Extend ys) = Extend (xs ++ ys)
  mappend (Root x xs) (Extend ys) = Root x (xs ++ ys)
  mappend (Extend xs) (Root y ys) = Root y (xs ++ ys)
  mappend (Root x xs) (Root y ys) = Extend [Root x xs, Root y ys]

showTree :: Show a => Int -> BuildTree a -> String
showTree i = \case 
  Empty -> "Empty"
  Root x [] -> show x
  Root x xs -> show x ++ "\n" ++ (intercalate "\n" $ map ((indent ++) . showTree (i+1)) xs)
  Extend xs -> "<no-root>\n" ++ (intercalate "\n" $ map ((indent ++) . showTree (i+1)) xs)
  where
    indent = replicate (i * 2) ' ' ++ "`-- "

instance Show a => Show (BuildTree a) where
  show = showTree 0

testTree :: Int -> Writer (BuildTree Int) ()
testTree 0 = root 0
testTree i = do
  root i
  _ <- branch $ testTree (i-1)
  branch $ testTree' (i-1)

testTree' :: Int -> Writer (BuildTree Int) ()
testTree' i 
  | i <= 0 = root i
  | otherwise = do
    root (negate i)
    _ <- branch $ testTree (i-1)
    branch $ testTree' (i-1)

type TypingState   = Integer -- |Just an integer for generating names
type TypingRead a  = TyCtx a
type TypingWrite a = BuildTree String

data TyExcept a
  = Type a Poly `CannotSubtype` Type a Poly
  | Name `OccursIn` Type a Poly
  | NameNotFound Name
  | CannotSplit (CtxElem a) (TyCtx a)
  | Other String
  deriving (Show, Eq)

tyExcept :: TyExcept a -> TypingM a r
tyExcept = throwError

cannotSubtype :: Type a Poly -> Type a Poly -> TypingM a r
cannotSubtype t1 t2 = tyExcept $ CannotSubtype t1 t2

occursIn :: Name -> Type a Poly -> TypingM a r
occursIn nm t = tyExcept $ OccursIn nm t

nameNotFound :: Name -> TypingM a r
nameNotFound nm = tyExcept $ NameNotFound nm

cannotSplit :: CtxElem a -> TyCtx a -> TypingM a r
cannotSplit el ctx = tyExcept $ CannotSplit el ctx

otherErr :: String -> TypingM a r
otherErr s = tyExcept $ Other s

newtype TypingM a r = Typ { unTypingM :: ExceptT (TyExcept a) (RWS (TypingRead a) (TypingWrite a) TypingState) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError (TyExcept a)
           , MonadState TypingState
           , MonadWriter (TypingWrite a)
           , MonadReader (TypingRead a)
           )

type TypingMRes a r = (Either (TyExcept a) r, TypingState, TypingWrite a)

runTypingM :: TypingM a r -> TypingRead a -> TypingState -> TypingMRes a r
runTypingM tm r s = runRWS (runExceptT (unTypingM tm)) r s

-- -- the typing monad
-- newtype TypingM a r = TypingM { unTypingM :: RWST (TypingRead a) (TypingWrite a) TypingState (Except (TyExcept a)) r }
--   deriving ( Functor
--            , Applicative
--            , Monad
--            , MonadError (TyExcept a)
--            , MonadState TypingState
--            , MonadWriter (TypingWrite a)
--            , MonadReader (TypingRead a)
--            )

getCtx :: TypingM a (TyCtx a)
getCtx = ask

freshName :: TypingM a Name
freshName = do 
  i <- get
  modify (+ 1)
  pure $ MName i

runTypingM0 :: TypingM a r -> TypingRead a -> TypingMRes a r
runTypingM0 tm r = runTypingM tm r initState where
  initState = 0

-- runTypingM :: TypingM a r -> TypingRead a -> TypingState -> TypingMRes a r
-- runTypingM tm r s = runExcept $ runRWST (unTypingM tm) r s

runSubtypeOf0 :: Eq a => Type a 'Poly -> Type a 'Poly -> TypingMRes a (TyCtx a)
runSubtypeOf0 t1 t2 = runSubtypeOf emptyCtx t1 t2

runSubtypeOf :: Eq a => TyCtx a -> Type a 'Poly -> Type a 'Poly -> TypingMRes a (TyCtx a)
runSubtypeOf ctx t1 t2 = runTypingM (t1 `subtypeOf` t2) ctx 0


substCtx :: Eq a => TyCtx a -> Type a Poly -> TypingM a (Type a Poly)
substCtx ctx (A a ty) = 
  case ty of
    TFree x -> pure $ A a $ TFree x
    TExists x -> 
      case findAssigned x ctx of
        Just tau -> pure $ asPolytype tau
        Nothing
          | Exists x `isInContext` ctx -> pure $ A a $ TExists x
          | otherwise                  -> otherErr $ "existential " ++ show x ++ " not in context during substitution"

    t1 `TApp` t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure $ A a $ t1 `TApp` t2
    
    t1 :->: t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure $ A a $ t1 :->: t2
    
    Forall x t -> do
      t' <- substCtx ctx t
      pure $ A a $ Forall x t'

-- | drop until an element `el` is encountered in the context. Also drops `el`
dropTil :: Eq a => CtxElem a -> TyCtx a -> TyCtx a
dropTil el (Gamma xs) = Gamma $ tl $ dropWhile (/= el) xs where
  tl []     = []
  tl (_:ys) = ys

-- again, since contexts are "reversed" notationally, this does not yield 
-- we switch ys and zs in the definition
splitCtx' :: Eq a => CtxElem a -> TyCtx a -> Maybe (TyCtx a, CtxElem a, TyCtx a)
splitCtx' el ctx@(Gamma xs) =
  case break (== el) xs of
    (_, [])    -> Nothing
    (ys, z:zs) -> pure (Gamma zs, z, Gamma ys)

splitCtx :: Eq a => CtxElem a -> TyCtx a -> TypingM a (TyCtx a, CtxElem a, TyCtx a)
splitCtx el ctx =
  case splitCtx' el ctx of
    Nothing -> cannotSplit el ctx
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
before' :: Eq a => CtxElem a -> CtxElem a -> TyCtx a -> Bool
before' alpha beta (Gamma ctx) = (beta `comesBefore` alpha) ctx False False where
  comesBefore x y [] xr yr = yr
  comesBefore x y (a:as) False False
    | x == a     = comesBefore x y as True False
    | y == a     = False
    | otherwise = comesBefore x y as False False
  comesBefore x y (a:as) True False
    | x == a = False
    | y == a = True
    | otherwise = comesBefore x y as True False
  comesBefore _ _ _ _ _ = False

before :: Eq a => CtxElem a -> CtxElem a -> TypingM a Bool
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
    Nothing  -> nameNotFound nm
    Just ctx' -> pure ctx'

insertAt' :: Eq a => CtxElem a -> TyCtx a -> TyCtx a -> Maybe (TyCtx a)
insertAt' at insertee into = do
  (l, _, r) <- splitCtx' at into
  pure $ l <++ insertee <++ r


-- Under input context Γ, instantiate α^ such that α^ <: A, with output context ∆
instL :: Eq a => Name -> Type a Poly -> TypingM a (TyCtx a)
-- InstLSolve
instL ahat (asMonotype -> Just mty) = do
  root $ "InstLSolve"
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

instR :: Eq a => Type a Poly -> Name -> TypingM a (TyCtx a)
-- InstRSolve
instR (asMonotype -> Just mty) ahat = do
  root $ "InstRSolve"
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
subtypeOf :: Eq a => Type a Poly -> Type a Poly -> TypingM a (TyCtx a)
subtypeOf ty1@(A _ typ1) ty2@(A _ typ2) = subtypeOf' typ1 typ2 where
  -- <:Var
  subtypeOf' (TFree x) (TFree x')
        | x == x'    = root "<:Var" *> getCtx
        | otherwise = extend "<:Var" *> cannotSubtype ty1 ty2
  
  -- <:Exvar
  subtypeOf' (TExists a) (TExists a') =
    root "<:Exvar" *> case () of
      _ | a == a' -> do 
          ctx <- getCtx
          if Exists a `isInContext` ctx
            then pure ctx
            else nameNotFound a
        | otherwise -> cannotSubtype ty1 ty2

  -- <:->
  subtypeOf' (a1 :->: a2) (b1 :->: b2) = do
    root $ "<:->"
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
    | ahat `inFreeVars` ty2 = root "InstantiateL" *> occursIn ahat ty2
    | otherwise = do 
      ctx <- getCtx
      if (Exists ahat) `isInContext` ctx 
        then do 
          root "InstantiateL"
          r <- branch (ahat `instL` ty2)
          pure r
        else nameNotFound ahat

  -- <:InstantiateR
  subtypeOf' _ (TExists ahat)
    | ahat `inFreeVars` ty1 = root "InstantiateR" *> occursIn ahat ty1
    | otherwise = do 
      ctx <- getCtx
      if (Exists ahat) `isInContext` ctx 
        then do 
          root "InstantiateR"
          r <- branch (ty1 `instR` ahat)
          pure r
        else nameNotFound ahat
  
  subtypeOf' t1 t2 = cannotSubtype ty1 ty2