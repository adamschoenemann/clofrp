{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module CloTT.Check.Poly where

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.AST.Parsed
import Control.Monad.RWS.Strict
import Control.Monad.Except

data CtxElem a
  = Uni Name -- ^ Universal
  | Exists Name -- ^ Existential
  | Name `HasType` Type a Poly -- ^ x : A
  | Name `Assigned` Type a Mono -- ^ a = t
  | Marker Name -- ^ |>a
  deriving (Show, Eq)

exists :: Name -> CtxElem a
exists = Exists

marker :: Name -> CtxElem a
marker = Marker

uni :: Name -> CtxElem a
uni = Uni

newtype TyCtx a = Gamma [CtxElem a]
  deriving (Show, Eq)

-- Lists are left-prepend but contexts are right-append
-- It doesn't matter, so we just pretend that we right-append stuff,
-- yet put it at the head 

infixl 5 <+
(<+) :: TyCtx a -> CtxElem a -> TyCtx a
Gamma xs <+ x = Gamma (x : xs)

infixl <++
(<++) :: TyCtx a -> TyCtx a -> TyCtx a
Gamma xs <++ Gamma ys = Gamma (ys ++ xs)

-- FIXME: We don't want to depend on (Eq a) since we do not consider the annotations
-- for equality. But I don't want to override the default Eq, because it is good
-- for testing purposes
isInContext :: Eq a => CtxElem a -> TyCtx a -> Bool
isInContext el (Gamma xs) = el `elem` xs

-- just an integer for generating names
type TypingState  = Integer
type TypingRead a = TyCtx a

data TyExcept a
  = Type a Poly `CannotSubtype` Type a Poly
  | Name `OccursIn` Type a Poly
  | NameNotFound Name
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

-- the typing monad
newtype TypingM a r = TypingM { unTypingM :: RWST (TypingRead a) () TypingState (Except (TyExcept a)) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError (TyExcept a)
           , MonadState TypingState
           , MonadWriter ()
           , MonadReader (TypingRead a)
           )

-- TODO: Consider how to avoid name capture (alpha renaming probably)
subtypeOf :: Eq a => Type a Poly -> Type a Poly -> TypingM a (TyCtx a)
subtypeOf ty1@(A _ t1) ty2@(A _ t2) = subtypeOf' t1 t2 where
  -- <:Var
  subtypeOf' (TFree x) (TFree x')
    | x == x'    = ask
    | otherwise = cannotSubtype ty1 ty2
  
  -- <:Exvar
  subtypeOf' (TExists a) (TExists a')
    | a == a' = ask
    | otherwise = cannotSubtype ty1 ty2

  -- <:->
  subtypeOf' (a1 :->: a2) (b1 :->: b2) = do
    ctx' <- b1 `subtypeOf` a1
    local (const ctx') $ (substCtx ctx' a2) `subtypeOf'` (substCtx ctx' b2)

  -- <:\/L
  subtypeOf' (Forall a (A _ t1)) t2 = do
    ctx' <- local (\g -> g <+ marker a <+ exists a) $ (subst (exists a) a t1) `subtypeOf'` t2
    pure $ dropTil (marker a) ctx'

  -- <:\/R
  subtypeOf' t1 (Forall a (A _ t2)) = do
    ctx' <- local (\g -> g <+ uni a) $ t1 `subtypeOf'` t2
    pure $ dropTil (uni a) ctx'
  
  -- <:InstantiateL
  subtypeOf' (TExists ahat) _
    | ahat `inFreeVars` ty2 = occursIn ahat ty2
    | otherwise = do 
      ctx <- ask
      if (Exists ahat) `isInContext` ctx 
        then ahat `instL` ty2
        else nameNotFound ahat

  -- <:InstantiateR
  subtypeOf' _ (TExists ahat)
    | ahat `inFreeVars` ty1 = occursIn ahat ty1
    | otherwise = do 
      ctx <- ask
      if (Exists ahat) `isInContext` ctx 
        then ty1 `instR` ahat
        else nameNotFound ahat

substCtx = undefined
dropTil = undefined
subst = undefined
instL = undefined
instR = undefined