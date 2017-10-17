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

module CloTT.Check.Poly.TypingM where

import Control.Monad.RWS.Strict hiding ((<>))
import Control.Monad.Except
import Control.Monad.State ()
import Data.String (fromString)

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.AST.Parsed hiding (exists)
import CloTT.Pretty
import CloTT.Check.Poly.Contexts

branch :: Pretty r => TypingM a r -> TypingM a r
branch comp = do
  i <- gets level
  modify $ \s -> s { level = i + 1 }
  r <- comp
  -- tell [(i+1, "≜" <+> pretty r)]
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
     , trClocks :: ClockCtx a
     }

instance Monoid (TypingRead a) where
  mempty = TR mempty mempty mempty mempty mempty
  mappend (TR c1 f1 k1 d1 clk1) (TR c2 f2 k2 d2 clk2) =
    TR { trCtx    = mappend c1 c2
       , trFree   = mappend f1 f2 
       , trKinds  = mappend k1 k2
       , trDestrs = mappend d1 d2
       , trClocks = mappend clk1 clk2
       }
  

type TypingWrite a = [(Integer, Doc ())]
type TypingErr a = (TyExcept a, TyCtx a)

showTree :: TypingWrite a -> String
showTree = showW 90 . prettyTree

prettyTree :: TypingWrite a -> Doc ()
prettyTree = vcat . map fn where
  fn (i, doc) = indent (fromInteger $ i * 2) doc

data TyExcept a
  = Type a Poly `CannotSubtype` Type a Poly
  | Name `OccursIn` Type a Poly
  | NameNotFound Name
  | CannotSplit (CtxElem a) (TyCtx a)
  | CannotSynthesize (Expr a)
  | CannotAppSynthesize (Type a Poly) (Expr a)
  | NotWfType (Type a Poly)
  | NotWfContext (CtxElem a)
  | PartialAliasApp (Alias a)
  | Other String
  | Decorate (TyExcept a) (TyExcept a)
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
    PartialAliasApp al       -> PartialAliasApp (unann al)
    Other s                  -> Other s
    Decorate outer inner     -> Decorate (unann outer) (unann inner)

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
    PartialAliasApp al       -> "Partial type-alias application of alias " <+> pretty al
    Other s                  -> "Other error:" <+> fromString s
    Decorate outer inner     -> pretty outer <> hardline <> "Caused by:" <> softline <> pretty inner

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

notWfContext :: CtxElem a -> TypingM a r
notWfContext el = tyExcept $ NotWfContext el

cannotSplit :: CtxElem a -> TyCtx a -> TypingM a r
cannotSplit el ctx = tyExcept $ CannotSplit el ctx

otherErr :: String -> TypingM a r
otherErr s = tyExcept $ Other s

partialAliasApp :: Alias a -> TypingM a r
partialAliasApp al = tyExcept $ PartialAliasApp al

decorateErr :: TypingM a r -> TyExcept a -> TypingM a r
decorateErr tm outer = tm `catchError` (\(inner,ctx) -> tyExcept $ Decorate outer inner)

errIf :: TypingM a r -> (r -> Bool) -> (r -> TyExcept a) -> TypingM a ()
errIf c p fl = do
  r <- c
  if p r then (tyExcept $ fl r) else pure ()

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
initRead = TR { trFree = mempty, trCtx = mempty, trKinds = mempty, trDestrs = mempty, trClocks = mempty }

getCtx :: TypingM a (TyCtx a)
getCtx = asks trCtx

getFCtx :: TypingM a (FreeCtx a)
getFCtx = asks trFree

getDCtx :: TypingM a (DestrCtx a)
getDCtx = asks trDestrs

getKCtx :: TypingM a (KindCtx a)
getKCtx = asks trKinds

getCCtx :: TypingM a (ClockCtx a)
getCCtx = asks trClocks

withCtx :: (TyCtx a -> TyCtx a) -> TypingM a r -> TypingM a r
withCtx fn = local fn' where
  fn' rd = rd { trCtx = fn (trCtx rd) }

withFCtx :: (FreeCtx a -> FreeCtx a) -> TypingM a r -> TypingM a r
withFCtx fn = local fn' where
  fn' rd = rd { trFree = fn (trFree rd) }

withKCtx :: (KindCtx a -> KindCtx a) -> TypingM a r -> TypingM a r
withKCtx fn = local fn' where
  fn' rd = rd { trKinds = fn (trKinds rd) }

withCCtx :: (ClockCtx a -> ClockCtx a) -> TypingM a r -> TypingM a r
withCCtx fn = local fn' where
  fn' rd = rd { trClocks = fn (trClocks rd) }

freshName :: TypingM a Name
freshName = do 
  i <- gets names
  modify $ \s -> s {names = names s + 1}
  pure $ MName i

initState :: TypingState
initState = TS 0 0

runTypingM0 :: TypingM a r -> TypingRead a -> TypingMRes a r
runTypingM0 tm r = runTypingM tm r initState