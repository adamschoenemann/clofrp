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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}

module CloTT.Check.Poly where

import Control.Monad.RWS.Strict hiding ((<>))
import Control.Monad.Except
import Control.Monad.State
import Data.List (break, intercalate, find)
import Control.Monad (foldM)
import Data.Foldable (foldlM, foldrM)
import Debug.Trace
import Data.Maybe (isJust)
import Data.Data
import Data.Char (isUpper)
import Data.String (fromString)
import Control.Applicative ((<|>))
import Data.Text.Prettyprint.Doc
import Control.Monad (foldM)
import GHC.Exts (IsList(..))
import qualified Data.Map.Strict as M

import CloTT.AST.Name
import CloTT.Context
import CloTT.Annotated
import CloTT.AST.Parsed hiding (exists)
import CloTT.Pretty

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

-- A destructor which is elaborated from a pattern
data Destr a = Destr
  { name   :: Name
  , typ    :: Type a Poly
  , bound  :: [Name]
  , args   :: [Type a Poly]
  } deriving (Show, Eq, Data, Typeable)

-- Free contexts contains "global" mappings from names to types
newtype FreeCtx a = FreeCtx { unFreeCtx :: M.Map Name (Type a Poly) }
  deriving (Show, Eq, Monoid, Data)

instance (IsList (FreeCtx a)) where
  type Item (FreeCtx a) = (Name, Type a Poly)
  fromList xs = FreeCtx $ M.fromList xs
  toList (FreeCtx m) = M.toList m

instance Context (FreeCtx a) where
  type Elem (FreeCtx a) = Type a Poly
  type Key (FreeCtx a)  = Name
  extend nm ty (FreeCtx m) = FreeCtx $ M.insert nm ty m
  isMemberOf nm (FreeCtx m) = M.member nm m
  query x (FreeCtx m) = M.lookup x m

-- Kind context contains "global" mappings from type-names to kinds
newtype KindCtx a = KindCtx { unKundCtx :: M.Map Name Kind }
  deriving (Show, Eq, Monoid, Data)

instance Context (KindCtx a) where
  type Elem (KindCtx a) = Kind
  type Key (KindCtx a)  = Name
  extend nm ty (KindCtx m) = KindCtx $ M.insert nm ty m
  isMemberOf nm (KindCtx m) = M.member nm m
  query x (KindCtx m) = M.lookup x m

instance (IsList (KindCtx a)) where
  type Item (KindCtx a) = (Name, Kind)
  fromList xs = KindCtx $ M.fromList xs
  toList (KindCtx m) = M.toList m

instance Pretty (KindCtx a) where
  pretty (KindCtx m) = enclose "[" "]" $ cat $ punctuate ", " $ map fn $ toList m where
    fn (k, v) = pretty k <+> "↦" <+> pretty v 


-- context of destructors 
newtype DestrCtx a = DestrCtx { unDestrCtx :: M.Map Name (Destr a) }
  deriving (Show, Eq, Monoid, Data)

instance Context (DestrCtx a) where
  type Elem (DestrCtx a) = Destr a
  type Key (DestrCtx a)  = Name
  extend nm ty (DestrCtx m) = DestrCtx $ M.insert nm ty m
  isMemberOf nm (DestrCtx m) = M.member nm m
  query x (DestrCtx m) = M.lookup x m

instance (IsList (DestrCtx a)) where
  type Item (DestrCtx a) = (Name, Destr a)
  fromList xs = DestrCtx $ M.fromList xs
  toList (DestrCtx m) = M.toList m

-- instance Pretty (DestrCtx a) where
--   pretty (DestrCtx m) = enclose "[" "]" $ cat $ punctuate ", " $ map fn $ toList m where
--     fn (k, v) = pretty k <+> "↦" <+> pretty v 



infix 1 |->
(|->) :: a -> b -> (a,b)
x |-> y = (x,y)

-- Typing context contains local variables and stuff
newtype TyCtx a = Gamma { unGamma :: [CtxElem a] }
  deriving (Eq)

instance Show (TyCtx a) where
  show gamma = showW 80 (pretty gamma)

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

instance Monoid (TyCtx a) where
  mempty = emptyCtx
  mappend = (<++)

isInContext :: CtxElem a -> TyCtx a -> Bool
isInContext el (Gamma xs) = isJust $ find (\x -> unann el == unann x) xs

isInFContext :: Name -> FreeCtx a -> Bool
isInFContext = isMemberOf

isInKContext :: Name -> KindCtx a -> Bool
isInKContext = isMemberOf

-- A type is wellformed
-- this one, validType and kindOf should probably be merged somehow...
isWfTypeIn' :: Type a Poly -> KindCtx a -> TyCtx a -> Bool
isWfTypeIn' (A ann ty) kctx ctx =
  -- trace ("isWfTypeIn'" ++ (show $ unann ty)) $
  case ty of
    -- UFreeWF
    TFree x -> x `isMemberOf` kctx
    -- UVarWF
    TVar x -> isJust $ ctxFind (freePred x) ctx
    -- EvarWF and SolvedEvarWF
    TExists alpha -> isJust $ ctxFind (expred $ alpha) ctx
    -- ArrowWF
    t1 :->: t2 -> isWfTypeIn' t1 kctx ctx && isWfTypeIn' t2 kctx ctx
    -- ForallWF
    Forall x t -> isWfTypeIn' t kctx (ctx <+ Uni x)
    -- TAppWF. FIXME Should check kinds correct kinds as well.
    TApp t1 t2 -> isWfTypeIn' t1 kctx ctx && isWfTypeIn' t2 kctx ctx
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

elemBy :: (a -> Bool) -> [a] -> Bool
elemBy fn = isJust . find fn

findAssigned :: Name -> TyCtx a -> Maybe (Type a Mono)
findAssigned nm (Gamma xs) = findMap fn xs >>= asMonotype where
  fn (nm' := ty) | nm == nm' = pure ty
  fn _                       = Nothing

hasTypeInCtx :: Name -> TyCtx a -> Maybe (Type a Poly)
hasTypeInCtx nm (Gamma xs) = findMap fn xs where
  fn (nm' `HasType` ty) | nm == nm' = pure ty
  fn _                             = Nothing

hasTypeInFCtx :: Name -> FreeCtx a -> Maybe (Type a Poly)
hasTypeInFCtx nm (FreeCtx m) = M.lookup nm m

lookupKind :: Name -> KindCtx a -> Maybe (Kind)
lookupKind nm (KindCtx m) = M.lookup nm m

addK :: Name -> Kind -> KindCtx a -> KindCtx a
addK nm k (KindCtx m) = KindCtx $ M.insert nm k m

branch :: TypingM a r -> TypingM a r
branch comp = do
  i <- gets level
  modify $ \s -> s { level = i + 1 }
  r <- comp
  modify $ \s -> s { level = i }
  pure r

root :: Doc () -> TypingM a ()
root x = gets level >>= \l -> tell [(l,x)]

data TypingState   = 
  TS { names :: Integer -- |Just an integer for generating names
     , level :: Integer
     }

data TypingRead a  = 
  TR { trCtx :: TyCtx a
     , trFree :: FreeCtx a
     , trKinds :: KindCtx a
     , trDestrs :: DestrCtx a
     }

instance Monoid (TypingRead a) where
  mempty = TR mempty mempty mempty mempty
  mappend (TR c1 f1 k1 d1) (TR c2 f2 k2 d2) =
    TR { trCtx    = mappend c1 c2
       , trFree   = mappend f1 f2 
       , trKinds  = mappend k1 k2
       , trDestrs = mappend d1 d2
       }
  
emptyFCtx :: FreeCtx a
emptyFCtx = FreeCtx (M.empty)

emptyKCtx :: KindCtx a
emptyKCtx = KindCtx (M.empty)

type TypingWrite a = [(Integer, Doc ())]
type TypingErr a = (TyExcept a, TyCtx a)

showTree :: TypingWrite a -> String
showTree = showW 90 . prettyTree

prettyTree :: TypingWrite a -> Doc ()
prettyTree = vcat . map fn where
  fn (i, doc) = indent (fromInteger $ i * 2) doc
-- prettyTree [] = ""
-- prettyTree ((i,s):xs) = indented ++ showTree xs where
  -- indented = unlines $ map (replicate (fromIntegral (i * 4)) ' ' ++) $ lines s

data TyExcept a
  = Type a Poly `CannotSubtype` Type a Poly
  | Name `OccursIn` Type a Poly
  | NameNotFound Name
  | CannotSplit (CtxElem a) (TyCtx a)
  | CannotSynthesize (Expr a)
  | CannotAppSynthesize (Type a Poly) (Expr a)
  | NotWfType (Type a Poly)
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
    NotWfType ty             -> NotWfType (unann ty)
    Other s                  -> Other s

instance Pretty (TyExcept a) where
  pretty = \case
    ty `CannotSubtype` ty'   -> pretty ty <+> "cannot subtype" <+> pretty ty'
    nm `OccursIn` ty         -> pretty nm <+> "occurs in" <+> pretty ty
    NameNotFound x           -> "Cannot find name" <+> pretty x
    CannotSplit el ctx       -> "Cannot split" <+> pretty ctx <+> "at" <+> pretty el
    CannotSynthesize e       -> "Cannot synthesize" <+> pretty e
    CannotAppSynthesize ty e -> "Cannot app_synthesize" <+> pretty ty <+> "•" <+> pretty e
    NotWfType ty             -> pretty ty <+> "is not well-formed"
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

notWfType :: Type a Poly -> TypingM a r
notWfType ty = tyExcept $ NotWfType ty

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

initRead :: TypingRead a 
initRead = TR { trFree = emptyFCtx, trCtx = emptyCtx, trKinds = emptyKCtx, trDestrs = mempty }

getCtx :: TypingM a (TyCtx a)
getCtx = asks trCtx

getFCtx :: TypingM a (FreeCtx a)
getFCtx = asks trFree

getDCtx :: TypingM a (DestrCtx a)
getDCtx = asks trDestrs

getKCtx :: TypingM a (KindCtx a)
getKCtx = asks trKinds

withCtx :: (TyCtx a -> TyCtx a) -> TypingM a r -> TypingM a r
withCtx fn = local fn' where
  fn' rd = rd { trCtx = fn (trCtx rd) }

withFCtx :: (FreeCtx a -> FreeCtx a) -> TypingM a r -> TypingM a r
withFCtx fn = local fn' where
  fn' rd = rd { trFree = fn (trFree rd) }

withKCtx :: (KindCtx a -> KindCtx a) -> TypingM a r -> TypingM a r
withKCtx fn = local fn' where
  fn' rd = rd { trKinds = fn (trKinds rd) }

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
    Just x  -> do 
      -- traceM $ "splitCtx " ++ show el ++ ":  " ++ show ctx ++ " ---> " ++ show x
      pure x

subst :: Type a Poly -> Name -> Type a Poly -> Type a Poly
subst x forY (A a inTy) = 
  case inTy of
    TFree y     | y == forY  -> x
                | otherwise -> A a $ TFree y

    TVar y      | y == forY  -> x
                | otherwise -> A a $ TVar y

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

-- Check if a context is well-formed
wfContext :: forall a. KindCtx a -> TyCtx a -> Bool
wfContext kctx (Gamma ctx) = isJust $ foldr fn (Just []) ctx where
  fn :: CtxElem a -> Maybe [CtxElem a] -> Maybe [CtxElem a]
  fn el accM = accM >>= (\acc -> if checkIt acc el then Just (el : acc) else Nothing)

  elem' f xs = isJust $ find (\x -> f (unann x)) xs
  checkIt acc = \case
    Uni nm          -> notInDom nm
    Exists nm       -> notInDom nm
    nm `HasType` ty -> notInDom nm && ((asPolytype ty `isWfTypeIn'` kctx) (Gamma acc))
    nm := ty        -> notInDom nm && ((asPolytype ty `isWfTypeIn'` kctx) (Gamma acc))
    Marker nm       -> notInDom nm && not ((\x -> Marker nm == x) `elem'` acc)
    where
      notInDom nm = not $ (\x -> Uni nm == x || Exists nm == x) `elem'` acc


-- assign an unsolved variable to a type in a context
-- TODO: Optimize 
assign' :: Name -> Type a Mono -> KindCtx a -> TyCtx a -> Either String (TyCtx a)
assign' nm ty kctx (Gamma ctx) =
  case foldr fn ([], False) ctx of
    (xs, True)
      | wfContext kctx (Gamma xs) -> Right (Gamma xs)
      | otherwise                 -> Left ("Ctx not well-formed: " ++ show (pretty (Gamma xs)))
    (xs, False)                   -> Left "Didn't assign anything" 
  where
    fn (Exists nm') (xs, _) | nm == nm' = (nm := ty : xs, True)
    fn x (xs, b)                        = (x : xs, b)

assign :: Name -> Type a Mono -> TypingM a (TyCtx a)
assign nm ty = do
  ctx <- getCtx
  kctx <- getKCtx
  case assign' nm ty kctx ctx of
    Left err  -> root "assign" *> otherErr err
    Right ctx' -> do 
      -- traceM $ showW 80 $ "assign" <+> pretty nm <+> pretty ty <+> pretty ctx <+> "---->" <+> pretty ctx'
      pure ctx'

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

-- Infer the kind of a type expression
kindOf' :: KindCtx a -> Type a Poly -> Either String Kind
kindOf' kctx (A _ t) =
  case t of
    TFree v -> maybe (notFound v) pure $ lookupKind v kctx
    
    -- should look up kind in local kctx
    TVar  v -> maybe (notFound v) pure $ lookupKind v kctx

    -- should look up kind in local kctx
    TExists  v -> maybe (notFound v) pure $ lookupKind v kctx

    TApp t1 t2 -> do
      k1 <- kindOf' kctx t1
      k2 <- kindOf' kctx t2
      case (k1, k2) of
        (k11 :->*: k12, k2')
          | k11 == k2' -> pure k12
          | otherwise  -> 
              Left $ "Expected " ++ pps t2 ++ " to have kind " ++ pps k11
        (_k1', _) -> Left $ "Expected " ++ pps t1 ++ " to be a type constructor"

    t1 :->: t2 -> do
      k1 <- kindOf' kctx t1
      k2 <- kindOf' kctx t2
      case (k1, k2) of
        (Star, Star) -> pure Star
        (k1', k2')   -> Left $ "Both operands in arrow types must have kind *, but had " 
                     ++ pps k1' ++ " and " ++ pps k2' ++ " in " ++ pps t
    
    Forall v tau -> kindOf' (addK v Star kctx) tau
  where
    notFound v = Left $ "Type " ++ pps v ++ " not found in context."

-- Types are only valid if they have kind *
validType' :: KindCtx a -> Type a Poly -> Bool
validType' kctx t = do
  case kindOf' kctx t of
    Right Star -> True
    Right k    -> trace ((show $ unann t) ++ " is not valid") $ False
    Left  err  -> trace err $ False

validType :: KindCtx a -> Type a Poly -> TypingM a ()
validType kctx t = do
  case kindOf' kctx t of
    Right Star -> pure ()
    Right k    -> otherErr $ show $ pretty t <+> "has kind" <+> pretty k <+> "but expected *"
    Left err   -> otherErr $ err

asMonotypeEither :: Type a s -> Either String (Type a Mono)
asMonotypeEither = maybe (Left "asMonotype") Right . asMonotype

-- Under input context Γ, instantiate α^ such that α^ <: A, with output context ∆
instL :: Name -> Type a Poly -> TypingM a (TyCtx a)
-- InstLSolve
instL ahat ty@(A a ty') = do 
  ctx <- getCtx
  kctx <- getKCtx
  case (\t -> assign' ahat t kctx ctx) =<< asMonotypeEither ty of 
    Right ctx' -> do 
      root $ "[InstLSolve]" <+> "^" <> pretty ahat <+> "=" <+> pretty ty <+> "in" <+> pretty ctx
      pure ctx'

    Left err  -> case ty' of
      -- InstLReach
      TExists bhat -> do
        root $ "[InstLReach]"
        Exists ahat `before` Exists bhat >>= \case
          True -> assign bhat (A a $ TExists ahat)
          False -> otherErr $ "InstLReach"

      -- InstLArr
      t1 :->: t2 -> do
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
        root $ "[InstLAllR]" <+> pretty ahat <+> ":<=" <+> pretty bty <+> "in" <+> pretty ctx
        beta' <- freshName
        let bty' = subst (A a $ TFree beta') beta bty
        ctx' <- withCtx (\g -> g <+ uni beta') $ branch (ahat `instL` bty')
        (delta, _, delta') <- splitCtx (uni beta') ctx'
        pure delta

      -- InstLTApp. Identical to InstLArr
      TApp t1 t2 -> do
        root $ "[InstLTApp]" <+> pretty ty <+> ":<=" <+> pretty ahat
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
      
      _ -> do
        root $ "[InstLError]" <+> "^" <> pretty ahat <+> "=" <+> pretty ty
        otherErr $ showW 80 $ "[instL] Cannot instantiate" <+> pretty ahat <+> "to" <+> pretty ty <+> ". Cause:" <+> fromString err


instR :: Type a Poly -> Name -> TypingM a (TyCtx a)
-- InstRSolve
instR ty@(A a ty') ahat = do
  ctx <- getCtx
  kctx <- getKCtx
  case (\t -> assign' ahat t kctx ctx) =<< asMonotypeEither ty of
    Right ctx' -> do
      root $ "[InstRSolve]" <+> pretty ty <+> "=<:" <+> pretty ahat
      pure ctx'
      
    Left err -> case ty' of
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
        root $ "[InstRTApp]" <+> pretty ty <+> "=<:" <+> pretty ahat
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
      
      _ -> otherErr $ showW 80 $ "[instR] Cannot instantiate" <+> pretty ahat <+> "to" <+> pretty ty <+> ". Cause:" <+> fromString err

-- Under input context Γ, type A is a subtype of B, with output context ∆
-- A is a subtype of B iff A is more polymorphic than B
-- TODO: Consider how to avoid name capture (alpha renaming probably)
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
      kctx <- getKCtx
      if ((A ann1 $ TExists ahat) `isWfTypeIn'` kctx) ctx  -- also check if ahat is in free vars of ty2
        then do 
          root $ "[InstantiateL]" <+> "^" <> pretty ahat <+> ":<=" <+> pretty ty2 <+> "in" <+> pretty ctx
          r <- branch (ahat `instL` ty2)
          pure r
        else do
          root $ "[InstantiateL]" <+> pretty ahat <+> ":<=" <+> pretty ty2 <+> "|- NameNotFound"
                 <+> pretty ahat <+> " in " <+> pretty ctx
          nameNotFound ahat

  -- <:InstantiateR
  subtypeOf' _ (TExists ahat)
    | ahat `inFreeVars` ty1 = root ("[InstantiateR] OccursError in" <+> pretty ty1 <+> ">=:" <+> pretty ty2) *> occursIn ahat ty1
    | otherwise = do 
      ctx <- getCtx
      kctx <- getKCtx
      if ((A ann2 $ TExists ahat) `isWfTypeIn'` kctx) ctx 
        then do 
          root $ "[InstantiateR]" <+> pretty ty1 <+> "=<:" <+> "^" <> pretty ahat
          r <- branch (ty1 `instR` ahat)
          pure r
        else do
          root $ "[InstantiateR]" <+> pretty ty1 <+> "=<:" <+> pretty ahat <+> "|- NameNotFound"
                 <+> pretty ahat <+> "in" <+> pretty ctx
          nameNotFound ahat
  
  -- <:TApp
  subtypeOf' (TApp a1 a2) (TApp b1 b2) = do
    ctx <- getCtx
    root $ "[<:TApp]" <+> pretty ty1 <+> "<:" <+> pretty ty2 <+> "in" <+> pretty ctx
    theta <- branch $ a1 `subtypeOf` b1
    a2' <- substCtx theta a2
    b2' <- substCtx theta b2
    branch $ withCtx (const theta) $ a2' `subtypeOf` b2'

  subtypeOf' t1 t2 = do
    root $ "[SubtypeError!]" <+> (fromString . show . unann $ t1) <+> "<:" <+> (fromString . show . unann $ t2)
    -- root $ "[Error!]" <+> pretty t1 <+> "<:" <+> pretty t2
    cannotSubtype ty1 ty2

check :: Expr a -> Type a Poly -> TypingM a (TyCtx a)
check e@(A eann e') ty@(A tann ty') = check' e' ty' where
  -- 1I (PrimI)
  check' (Prim p) _ 
    | ty' =%= inferPrim p = root "[PrimI]" *> getCtx
  
  -- ∀I
  check' _ (Forall alpha aty) = do
    ctx <- getCtx
    root $ "[∀I]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
    alpha' <- freshName
    let aty' = subst (A tann $ TVar alpha') alpha aty
    (delta, _, _) <- splitCtx (Uni alpha') =<< withCtx (\g -> g <+ Uni alpha') (branch $ check e aty')
    pure delta
  
  -- ->I
  check' (Lam x Nothing e2) (aty :->: bty) = do
    ctx <- getCtx
    root $ "[->I]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
    let c = x `HasType` aty
    (delta, _, _) <- splitCtx c =<< withCtx (\g -> g <+ c) (branch $ check e2 bty)
    pure delta
  
  -- Case<=
  check' (Case e' clauses) _ = do
    root $ "[Case<=]" <+> pretty e <+> "<=" <+> pretty ty
    (pty, delta) <- branch $ synthesize e'
    -- traceM $ show $ pretty delta
    cty <- withCtx (const delta) $ branch $ checkCaseClauses pty clauses ty
    pure delta

  -- Sub
  check' _ _ = do
    ctx <- getCtx
    root $ "[Sub]" <+> pretty e <+> "<=" <+> pretty ty <+> "in" <+> pretty ctx
    (aty, theta) <- branch $ synthesize e
    branch $ root $ "[Info] Synthesized" <+> pretty (aty, theta)
    atysubst <- substCtx theta aty
    btysubst <- substCtx theta ty
    withCtx (const theta) $ branch $ atysubst `subtypeOf` btysubst
  
  checkCaseClauses :: Type a Poly -> [(Pat a, Expr a)] -> Type a Poly -> TypingM a ()
  checkCaseClauses pty clauses expected = traverse checkClause clauses *> pure () where
    checkClause (pat, expr) = do 
      ctx <- getCtx
      root $ "[CheckClause]" <+> pretty pat <+> "->" <+> pretty expr <+> "<=" <+> pretty expected <+> "in" <+> pretty ctx
      ctx' <- branch $ checkPat pat pty
      withCtx (const ctx') $ branch $ check expr expected



synthesize :: Expr a -> TypingM a (Type a Poly, TyCtx a)
synthesize expr@(A ann expr') = synthesize' expr' where
  -- Var
  synthesize' (Var nm) = do
    ctx <- getCtx
    fctx <- getFCtx
    kctx <- getKCtx
    case (nm `hasTypeInCtx` ctx <|> nm `hasTypeInFCtx` fctx) of
      Just ty 
        | (ty `isWfTypeIn'` kctx) ctx -> do 
            root $ "[Var]" <+> pretty expr <+> "=>" <+> pretty ty
            pure (ty, ctx)
        | otherwise -> do
            root $ "[Var]" <+> pretty nm <+> ":" <+> pretty ty <+> "is not wellformed"
                   <+> "in kctx: " <+> pretty kctx <+> softline <> "in ctx:" <+> pretty ctx
            notWfType ty

      Nothing -> root "[Var]" *> nameNotFound nm

  
  -- Anno
  synthesize' (Ann e ty) = do
    root $ "[Anno]" <+> pretty e <+> ":" <+> pretty ty
    _ <- branch $ check e ty
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
  
  -- ->E
  synthesize' (App e1 e2) = do
    ctx <- getCtx
    root $ "[->E]" <+> pretty expr <+> "in" <+> pretty ctx
    (ty1, theta) <- branch $ synthesize e1
    ty1subst <- substCtx theta ty1
    withCtx (const theta) $ branch $ applysynth ty1subst e2 

  -- Prim=>
  synthesize' (Prim p) = do
    let pt = inferPrim p
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

inferPrim :: Prim -> Type' a Poly
inferPrim p = TFree $ UName $ case p of
  Unit   -> "Unit"
  Bool _ -> "Bool"
  Nat _  -> "Nat"

-- in a context, check each clause against a type of (pattern, Maybe expression)
-- if second type is nothing, it is because we do not yet know which type to infer,
-- but we should know in first recursive call
-- DEPRECATED!
-- checkClauses :: (Type a Poly, Maybe (Type a Poly)) -> [(Pat a, Expr a)] -> TypingM a (Type a Poly)
-- checkClauses (_, mety) [] = 
--   case mety of 
--     Just ty -> pure ty
--     Nothing -> otherErr $ "case expressions must have at least one clause"
-- checkClauses (pty, mety) ((pat, e) : clauses) = do
--   root $ "[CheckClause]" <+> pretty pat <+> "->" <+> pretty e <+> "<=" <+> pretty mety
--   nctx <- checkPat pat pty
--   case mety of 
--     Just ety -> withCtx (const nctx) (branch $ check e ety) *> checkClauses (pty, mety) clauses
--     Nothing  -> do 
--       (ety, ctx) <- branch $ withCtx (const nctx) (synthesize e)
--       checkClauses (pty, Just ety) clauses

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
existentialize ann d = do
  (nms, d') <- foldrM folder ([], d) (bound d)
  ctx <- getCtx
  let ctx' = foldr (\n g -> g <+ Exists n) ctx nms
  pure (ctx', d')
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
      ctx' <- withCtx (const delta) $ branch $ etyp `patSubtypeOf` expected
      -- traceM (show $ pretty ctx')
      foldlM folder ctx' $ zip pats eargs
      where 
        folder acc (p, t) = do 
          t' <- substCtx acc t
          withCtx (const acc) $ checkPat p t'
  
-- like subtypeOf, but if the right operand is a forall a. t, we extend
-- the context with ̂a and subtype from t
patSubtypeOf :: Type a Poly -> Type a Poly -> TypingM a (TyCtx a)
patSubtypeOf ty1@(A ann1 ty1') ty2@(A ann2 ty2') =
  case (ty1', ty2') of
    (_, Forall nm t) -> do
      alpha <- freshName
      let t' = subst (A ann2 $ TExists alpha) nm $ t
      root $ "[PatSubtypeOf]" <+> pretty ty1 <+> ":p<" <+> pretty ty2
      withCtx (\g -> g <+ Exists alpha) $ branch $ ty1 `patSubtypeOf` t'

    _ -> ty1 `subtypeOf` ty2


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
        ctx' <- insertAt (Exists alpha) (emptyCtx <+ Exists a2 <+ Exists a1 <+ alpha := a1toa2)
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
  
  applysynth' _ = cannotAppSynthesize ty e

