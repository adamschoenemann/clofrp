{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module CloTT.Check.Poly.Contexts
  ( module CloTT.Check.Poly.Contexts
  , module CloTT.Check.Poly.Destr
  ) where

import Data.Data
import GHC.Exts (IsList(..))
import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M
import Data.List (break, find)
import Data.Maybe (isJust)

import CloTT.Check.Poly.Destr
import CloTT.AST.Parsed hiding (exists)
import CloTT.Context
import CloTT.Annotated
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

-- Free contexts contains "global" mappings from names to types
newtype FreeCtx a = FreeCtx { unFreeCtx :: M.Map Name (Type a Poly) }
  deriving (Show, Eq, Monoid, Data)


mapFreeCtx :: (Type a Poly -> Type b Poly) -> FreeCtx a -> FreeCtx b
mapFreeCtx fn (FreeCtx m) = FreeCtx $ M.map fn m

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

-- Clock context contains mappings from names to clocks.
-- Since clocks are just names, we really just need a set here.
-- But, we'll just use a Map from Name to Unit. Is that a hack? Certainly.
newtype ClockCtx a = ClockCtx { unClockCtx :: M.Map Name () }
  deriving (Show, Eq, Monoid, Data)

instance Context (ClockCtx a) where
  type Elem (ClockCtx a) = ()
  type Key (ClockCtx a)  = Name
  extend nm ty (ClockCtx m) = ClockCtx $ M.insert nm ty m
  isMemberOf nm (ClockCtx m) = M.member nm m
  query x (ClockCtx m) = M.lookup x m

instance (IsList (ClockCtx a)) where
  type Item (ClockCtx a) = Name
  fromList xs = ClockCtx $ M.fromList (map (\x -> (x,())) xs)
  toList (ClockCtx m) = M.keys m

instance Pretty (ClockCtx a) where
  pretty (ClockCtx m) = enclose "[" "]" $ cat $ punctuate ", " $ map fn $ toList m where
    fn (k, v) = pretty k 

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
  mempty = Gamma []
  mappend = (<++)

isInContext :: CtxElem a -> TyCtx a -> Bool
isInContext el (Gamma xs) = isJust $ find (\x -> unann el == unann x) xs

isInFContext :: Name -> FreeCtx a -> Bool
isInFContext = isMemberOf

isInKContext :: Name -> KindCtx a -> Bool
isInKContext = isMemberOf



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

insertAt' :: CtxElem a -> TyCtx a -> TyCtx a -> Maybe (TyCtx a)
insertAt' at insertee into = do
  (l, _, r) <- splitCtx' at into
  pure $ l <++ insertee <++ r

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

-- A type is wellformed
-- this one, validType and kindOf should probably be merged somehow...
-- DEPRECATED in favor of checkWfType
isWfTypeIn' :: Type a Poly -> KindCtx a -> TyCtx a -> Bool
isWfTypeIn' (A ann ty) kctx ctx =
  -- trace ("isWfTypeIn'" ++ (show $ unann ty)) $
  case ty of
    -- UFreeWF
    TFree x -> x `isMemberOf` kctx
    -- UVarWF
    TVar x -> isJust $ ctxFind (varPred x) ctx
    -- EvarWF and SolvedEvarWF
    TExists alpha -> isJust $ ctxFind (expred $ alpha) ctx
    -- ArrowWF
    t1 :->: t2 -> isWfTypeIn' t1 kctx ctx && isWfTypeIn' t2 kctx ctx
    -- ForallWF
    Forall x t 
      | Just _ <- ctxFind (varPred x) ctx -> False
      | otherwise                         -> isWfTypeIn' t kctx (ctx <+ Uni x)
    -- TAppWF. FIXME Should check correct kinds as well.
    TApp t1 t2 -> isWfTypeIn' t1 kctx ctx && isWfTypeIn' t2 kctx ctx
    -- ClockWF
    -- Clock kappa t
  where 
    expred alpha = \case
      Exists alpha' -> alpha == alpha'
      alpha' := _   -> alpha == alpha' 
      _         -> False

    varPred x = \case
      Uni x' -> x == x'
      _      -> False
