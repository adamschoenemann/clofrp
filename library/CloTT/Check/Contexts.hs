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
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FunctionalDependencies #-}

module CloTT.Check.Contexts
  ( module CloTT.Check.Contexts
  , module CloTT.Context
  , module CloTT.Check.Destr
  ) where

import Data.Data
import GHC.Exts (IsList(..))
import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (break, find)
import Data.Maybe (isJust, catMaybes, listToMaybe)

import CloTT.Check.Destr
import CloTT.AST hiding (exists)
import CloTT.Context
import CloTT.Annotated
import CloTT.Pretty
import CloTT.Utils (findMap)

data Binding = LamB | LetB deriving (Eq, Show)

data CtxElem a
  -- | Universal  
  = Uni Name Kind 
  -- | Existential  
  | Exists Name Kind 
  -- | (λ?)x : A  
  | (Binding, Name) `HasType` Type a Poly 
  -- | a = t  
  | Name := Type a Mono 
  -- | |>a  
  | Marker Name 
  deriving Eq

instance Unann (CtxElem a) (CtxElem ()) where
  unann el = 
    case el of
      Uni nm k        -> Uni nm k
      Exists nm k     -> Exists nm k
      (b,nm) `HasType` ty -> (b,nm) `HasType` unann ty
      nm := ty        -> nm := unann ty
      Marker nm       -> Marker nm

instance Pretty (CtxElem a) where
  pretty = \case
    Uni nm Star -> pretty nm
    Uni nm k    -> parens (pretty nm <+> ":" <+> pretty k)
    Exists nm Star -> "^" <> pretty nm
    Exists nm k    -> parens ("^" <> pretty nm <+> ":" <+> pretty k)
    (b, nm) `HasType` ty ->
      pretty nm <+> p b <> ":" <+> pretty (unann ty) 
      where 
        p LamB = "λ"
        p LetB = ""

    nm := ty        -> "^" <> pretty nm <+> "=" <+> pretty (unann ty)
    Marker nm       -> "†" <> pretty nm

instance Show (CtxElem a) where
  show = show . pretty


exists :: Name -> CtxElem a
exists nm = Exists nm Star

marker :: Name -> CtxElem a
marker = Marker

uni :: Name -> CtxElem a
uni nm = Uni nm Star

(<\:) :: Name -> Type a Poly -> CtxElem a
x <\: t = (LamB, x) `HasType` t

(.:) :: Name -> Type a Poly -> CtxElem a
x .: t = (LetB, x) `HasType` t

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

-- context of instances of type-classes
data ClassInstance a = ClassInstance
  { ciClassName :: Name
  , ciInstanceTypeName :: Name
  , ciParams :: [Name]
  , ciDictionary :: M.Map Name (Type a Poly, Expr a)
  } deriving (Eq, Data, Typeable)

instance Pretty (ClassInstance a) where
  pretty (ClassInstance {ciClassName, ciParams, ciDictionary, ciInstanceTypeName}) = 
    "Instance" <+> tupled [pretty ciClassName, pretty ciInstanceTypeName, pretty ciParams, list $ M.elems $ M.map pretty ciDictionary]

instance Show (ClassInstance a) where
  show = show . pretty

newtype InstanceCtx a = InstanceCtx { unInstanceCtx :: M.Map Name [ClassInstance a] }
  deriving (Show, Eq, Monoid, Data, Typeable)

class HasInstances m a | m -> a where
  getInstances :: m (InstanceCtx a)

getInstancesOf :: (Monad m, HasInstances m a) => Name -> m [ClassInstance a]
getInstancesOf name = do
  is <- getInstances
  case M.lookup name (unInstanceCtx is) of
    Just is' -> pure is'
    Nothing  -> pure []

findInstanceOf :: (Monad m, HasInstances m a) => Name -> Type a Poly -> m (Maybe (ClassInstance a))
findInstanceOf className ty = do
  instances <- getInstancesOf className
  pure (listToMaybe . catMaybes $ map hasInstance instances)
  where
    hasInstance ci@(ClassInstance {ciInstanceTypeName = nm , ciParams = params}) = 
      case genPred nm params ty of
        True -> Just ci
        False -> Nothing

    -- FIXME: this is a crazy hack to resolve "type-class" instances by folding a predicate over
    -- the bound variables of a type constructor
    genPred tnm bnd = foldr folder (\x -> unann x == A () (TFree tnm)) bnd where
      folder b acc ty = 
        case ty of
          A _ (a `TApp` b) -> acc a
          _                -> False

-- instance Pretty (DestrCtx a) where
--   pretty (DestrCtx m) = enclose "[" "]" $ cat $ punctuate ", " $ map fn $ toList m where
--     fn (k, v) = pretty k <+> "↦" <+> pretty v 

-- Typing context contains local variables and stuff
newtype TyCtx a = Gamma { unGamma :: [CtxElem a] }
  deriving (Eq)

instance Show (TyCtx a) where
  show gamma = showW 80 (pretty gamma)

instance Pretty (TyCtx a) where
  pretty (Gamma xs) = 
    brackets $ concatWith (\x y -> x <+> softline' <> comma <> space <> y) $ map pretty (reverse xs)
    -- brackets $ column p where
    -- p c = concatWith (\x y -> nesting $ \n -> x <> nest (c - n) (softline' <> comma <> space <> y)) $ map pretty (reverse xs)
    -- list $ map pretty $ reverse xs

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

ctxFind :: (CtxElem a -> Bool) -> TyCtx a -> Maybe (CtxElem a)
ctxFind p (Gamma xs) = find p xs

lookupTy :: Name -> TyCtx a -> Maybe (Type a Poly)
lookupTy nm (Gamma xs) = findMap p xs where
  p ((_,nm') `HasType` ty) | nm' == nm = Just ty
  p _                  = Nothing

elemBy :: (a -> Bool) -> [a] -> Bool
elemBy fn = isJust . find fn

findAssigned :: Name -> TyCtx a -> Maybe (Type a Mono)
findAssigned nm (Gamma xs) = findMap fn xs >>= asMonotype where
  fn (nm' := ty) | nm == nm' = pure ty
  fn _                       = Nothing

isAssigned :: Name -> TyCtx a -> Bool
isAssigned = isJust .*. findAssigned where
  (.*.) = (.) . (.)

hasTypeInCtx :: Name -> TyCtx a -> Maybe (Type a Poly)
hasTypeInCtx nm (Gamma xs) = findMap fn xs where
  fn ((_,nm') `HasType` ty) | nm == nm' = pure ty
  fn _                             = Nothing

hasTypeInFCtx :: Name -> FreeCtx a -> Maybe (Type a Poly)
hasTypeInFCtx nm (FreeCtx m) = M.lookup nm m

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


insertAt' :: CtxElem a -> TyCtx a -> TyCtx a -> Maybe (TyCtx a)
insertAt' at insertee into = do
  (l, _, r) <- splitCtx' at into
  pure $ l <++ insertee <++ r

containsEVar :: TyCtx a -> Name -> Bool
containsEVar ctx alpha = isJust $ ctxFind expred ctx where
    expred = \case
      Exists alpha' _k -> alpha == alpha'
      alpha' := _   -> alpha == alpha' 
      _             -> False

containsTVar :: TyCtx a -> Name -> Bool
containsTVar ctx alpha = isJust $ ctxFind varPred ctx where
    varPred = \case
      Uni alpha' _k -> alpha == alpha'
      _          -> False

getUnsolved :: TyCtx a -> [(Name, Kind)]
getUnsolved (Gamma xs) = foldr fn [] xs where
  fn (Exists nm k) acc = (nm, k) : acc
  fn _ acc             = acc


  