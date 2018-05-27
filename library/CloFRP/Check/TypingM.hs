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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FunctionalDependencies #-}

module CloFRP.Check.TypingM where

import Control.Monad.RWS.Strict hiding ((<>))
import Control.Monad.Except
import Control.Monad.State ()
import Data.String (fromString)

import CloFRP.AST.Name
import CloFRP.Utils ((|->))
import CloFRP.Annotated
import CloFRP.AST hiding (exists)
import CloFRP.Pretty
import CloFRP.Check.Contexts

branch :: Pretty r => TypingM a r -> TypingM a r
branch comp = do
  i <- gets level
  modify $ \s -> s { level = i + 1 }
  r <- comp
  modify $ \s -> s { level = i }
  pure r

silentBranch :: Pretty r => TypingM a r -> TypingM a r
silentBranch comp = do
  i <- gets level
  t <- gets debugDerivationTree
  modify $ \s -> s { level = i + 1 }
  r <- comp
  modify $ \s -> s { level = i, debugDerivationTree = t }
  pure r

-- | Log that a rule of some name with some info was triggered
rule :: Doc () -> Doc () -> TypingM a ()
rule name info = do
  ctx <- getCtx
  root $ sep [brackets name <+> info, indent 4 (nest 3 ("in" <+> pretty ctx))]

tellDebugTree :: DerivationTree -> TypingM a ()
tellDebugTree dt =
  modify (\s -> s { debugDerivationTree = dt ++ debugDerivationTree s })

clearDebugTree :: TypingM a ()
clearDebugTree = modify (\st -> st { debugDerivationTree = [] })

root :: Doc () -> TypingM a ()
root x = gets level >>= \l -> tellDebugTree [(l,x)]

type DerivationTree = [(Integer, Doc ())]

-- |I used to have a MonadWriter but moved it to state
type TypingWrite a = DerivationTree 

-- Typing state
data TypingState   = 
  TS { names :: Integer -- |Just an integer for generating names
     , level :: Integer -- |For debugging
     , debugDerivationTree :: DerivationTree -- |For debugging
     }

-- Typing reader

data TypingRead a  = 
  TR { trCtx :: LocalCtx a
     , trFree :: FreeCtx a
     , trKinds :: KindCtx a
     , trDestrs :: DestrCtx a
     , trInstances :: InstanceCtx a
     }

instance Monoid (TypingRead a) where
  mempty = TR mempty mempty mempty mempty mempty 
  mappend (TR c1 f1 k1 d1 is1) (TR c2 f2 k2 d2 is2) =
    TR { trCtx    = mappend c1 c2
       , trFree   = mappend f1 f2 
       , trKinds  = mappend k1 k2
       , trDestrs = mappend d1 d2
       , trInstances = mappend is1 is2
       }
  

type TypingErr a = (TyExcept a, LocalCtx a)

showTree :: DerivationTree -> String
showTree = showW 90 . prettyTree

prettyTree :: DerivationTree -> Doc ()
prettyTree = vcat . map fn where
  fn (i, doc) = indent (fromInteger $ i * 2) doc

data TyExcept a
  = PolyType a `CannotSubtype` PolyType a
  | Name `OccursIn` PolyType a
  | NameNotFound Name
  | CannotSplit (CtxElem a) (LocalCtx a)
  | CannotSynthesize (Expr a)
  | CannotAppSynthesize (PolyType a) (Expr a)
  | NotWfType (PolyType a)
  | NotWfContext (CtxElem a)
  | PartialSynonymApp (Synonym a)
  | MutualRecursionErr Name
  | Other String
  | Decorate (TyExcept a) (TyExcept a)
  | UncoveredCases (Pat a)
  | UnreachableCases [Pat a]
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
    NotWfContext el          -> NotWfContext (unann el)
    PartialSynonymApp syn       -> PartialSynonymApp (unann syn)
    MutualRecursionErr nm    -> MutualRecursionErr nm
    Other s                  -> Other s
    Decorate outer inner     -> Decorate (unann outer) (unann inner)
    UncoveredCases pat       -> UncoveredCases (unann pat)
    UnreachableCases pat     -> UnreachableCases (map unann pat)

instance Pretty (TyExcept a) where
  pretty = \case
    ty `CannotSubtype` ty'   -> pretty ty <+> "cannot subtype" <+> pretty ty'
    nm `OccursIn` ty         -> pretty nm <+> "occurs in" <+> pretty ty
    NameNotFound x           -> "Cannot find name" <+> pretty x
    CannotSplit el ctx       -> "Cannot split" <+> pretty ctx <+> "at" <+> pretty el
    CannotSynthesize e       -> "Cannot synthesize" <+> pretty e
    CannotAppSynthesize ty e -> "Cannot app_synthesize" <+> pretty ty <+> "•" <+> pretty e
    NotWfType ty             -> pretty ty <+> "is not well-formed"
    NotWfContext el          -> "Context is not well-formed due to" <+> pretty el
    PartialSynonymApp syn       -> "Partial type-synonym application of synonym " <+> pretty syn
    MutualRecursionErr nm    -> pretty nm <+> "is mutually recursive with something else"
    Other s                  -> "Other error:" <+> fromString s
    UncoveredCases pat       -> "Pattern match is not exhaustive:" <+> pretty pat <+> "is not covered."
    UnreachableCases pat     -> "Cases" <+> pretty pat <+> "is unreachable"
    Decorate outer inner     -> pretty outer <> hardline <> "Caused by:" <> softline <> pretty inner

tyExcept :: TyExcept a -> TypingM a r
tyExcept err = do 
  ctx <- getCtx 
  throwError (err, ctx)

cannotSubtype :: PolyType a -> PolyType a -> TypingM a r
cannotSubtype t1 t2 = tyExcept $ CannotSubtype t1 t2

cannotSynthesize :: Expr a -> TypingM a r
cannotSynthesize e = tyExcept $ CannotSynthesize e

cannotAppSynthesize :: PolyType a -> Expr a -> TypingM a r
cannotAppSynthesize t e = tyExcept $ CannotAppSynthesize t e

occursIn :: Name -> PolyType a -> TypingM a r
occursIn nm t = tyExcept $ OccursIn nm t

nameNotFound :: Name -> TypingM a r
nameNotFound nm = tyExcept $ NameNotFound nm

notWfType :: PolyType a -> TypingM a r
notWfType ty = tyExcept $ NotWfType ty

notWfContext :: CtxElem a -> TypingM a r
notWfContext el = tyExcept $ NotWfContext el

cannotSplit :: CtxElem a -> LocalCtx a -> TypingM a r
cannotSplit el ctx = tyExcept $ CannotSplit el ctx

otherErr :: String -> TypingM a r
otherErr s = tyExcept $ Other s

partialSynonymApp :: Synonym a -> TypingM a r
partialSynonymApp syn = tyExcept $ PartialSynonymApp syn

decorateErr :: TypingM a r -> TyExcept a -> TypingM a r
decorateErr tm outer = tm `catchError` (\(inner, _ctx) -> tyExcept $ Decorate outer inner)

uncoveredCases :: Pat a -> TypingM a r
uncoveredCases = tyExcept . UncoveredCases

unreachableCases :: [Pat a] -> TypingM a r
unreachableCases = tyExcept . UnreachableCases

errIf :: TypingM a r -> (r -> Bool) -> (r -> TyExcept a) -> TypingM a ()
errIf c p fl = do
  r <- c
  if p r then (tyExcept $ fl r) else pure ()

newtype TypingM a r = Typ { unTypingM :: ExceptT (TypingErr a) (RWS (TypingRead a) () TypingState) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError (TypingErr a)
           , MonadState TypingState
           , MonadReader (TypingRead a)
           )

type TypingMRes a r = (Either (TypingErr a) r, TypingState, DerivationTree)

runTypingM :: TypingM a r -> TypingRead a -> TypingState -> TypingMRes a r
runTypingM tm r s = 
  let (res, st, _unit) = runRWS (runExceptT (unTypingM tm)) (r `mappend` initRead) s
  in (res, st, reverse $ debugDerivationTree st)

initRead :: TypingRead a 
initRead = 
  let initKinds = ["Int" |-> Star, "K0" |-> ClockK]
  in  TR { trFree = mempty, trCtx = mempty, trKinds = initKinds, trDestrs = mempty, trInstances = mempty }

getCtx :: TypingM a (LocalCtx a)
getCtx = asks trCtx

getFCtx :: TypingM a (FreeCtx a)
getFCtx = asks trFree

getDCtx :: TypingM a (DestrCtx a)
getDCtx = asks trDestrs

getKCtx :: TypingM a (KindCtx a)
getKCtx = asks trKinds

instance HasInstances (TypingM a) a where
  getInstances = asks trInstances

withCtx :: (LocalCtx a -> LocalCtx a) -> TypingM a r -> TypingM a r
withCtx fn = local fn' where
  fn' rd = rd { trCtx = fn (trCtx rd) }

withFCtx :: (FreeCtx a -> FreeCtx a) -> TypingM a r -> TypingM a r
withFCtx fn = local fn' where
  fn' rd = rd { trFree = fn (trFree rd) }

withKCtx :: (KindCtx a -> KindCtx a) -> TypingM a r -> TypingM a r
withKCtx fn = local fn' where
  fn' rd = rd { trKinds = fn (trKinds rd) }

fromEither :: Either String r -> TypingM a r
fromEither = either otherErr pure

-- withCCtx :: (ClockCtx a -> ClockCtx a) -> TypingM a r -> TypingM a r
-- withCCtx fn = local fn' where
--   fn' rd = rd { trClocks = fn (trClocks rd) }

freshName :: TypingM a Name
freshName = do 
  i <- gets names
  modify $ \s -> s {names = names s + 1}
  pure $ MName i

resetNameState :: TypingM a ()
resetNameState = do
  modify $ \s -> s {names = 0}
  pure ()

initState :: TypingState
initState = TS 0 0 []

runTypingM0 :: TypingM a r -> TypingRead a -> TypingMRes a r
runTypingM0 tm r = runTypingM tm r initState

-- | Lookup a type in a given context (lifted to TypingM monad)
lookupTyTM :: Name -> LocalCtx a -> TypingM a (PolyType a)
lookupTyTM nm c =
  case lookupTy nm c of
    Just t -> pure t
    Nothing -> nameNotFound nm

substCtx :: LocalCtx a -> PolyType a -> TypingM a (PolyType a)
substCtx ctx (A a ty) =
  case ty of
    TFree x -> pure $ A a $ TFree x
    TVar x  -> pure $ A a $ TVar  x
    TExists x ->
      case findAssigned x ctx of
        Just tau -> substCtx ctx (asPolytype tau) -- do it again to make substitutions simultaneous (transitive)
        Nothing
          | ctx `containsEVar` x -> pure $ A a $ TExists x
          | otherwise            -> 
              otherErr $ show $ "existential" <+> pretty x 
              <+> "not in context" <> line <> pretty ctx

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

-- | Attempt to convert a type to a monotype and lift it to the TypingM monad
asMonotypeTM :: Type a s -> TypingM a (MonoType a)
asMonotypeTM t = maybe (otherErr $ show $ pretty t <+> "is not a monotype") pure . asMonotype $ t