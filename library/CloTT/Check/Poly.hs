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

otherErr :: String -> TypingM a r
otherErr s = tyExcept $ Other s

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
    a2' <- substCtx ctx' a2
    b2' <- substCtx ctx' b2
    local (const ctx') $ a2' `subtypeOf` b2'

  -- <:\/L
  subtypeOf' (Forall nm (A at1 t1)) t2 = do
    ctx' <- local (\g -> g <+ marker nm <+ exists nm) $ (subst (A at1 $ TExists nm) nm (A at1 t1)) `subtypeOf` ty2
    pure $ dropTil (marker nm) ctx'

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

substCtx :: Eq a => TyCtx a -> Type a Poly -> TypingM a (Type a Poly)
substCtx ctx (A a ty) = A a <$> 
  case ty of
    TFree x -> pure $ TFree x
    TExists x 
      | Exists x `isInContext` ctx -> pure $ TFree x
      | otherwise                  -> otherErr $ "existential " ++ show x ++ " not in context during substitution"

    t1 `TApp` t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure $ t1 `TApp` t2
    
    t1 :->: t2 -> do
      t1' <- substCtx ctx t1
      t2' <- substCtx ctx t2
      pure $ t1 :->: t2
    
    Forall x t -> do
      t' <- substCtx ctx t
      pure $ Forall x t'

dropTil :: Eq a => CtxElem a -> TyCtx a -> TyCtx a
dropTil el (Gamma xs) = Gamma $ tl $ dropWhile (/= el) xs where
  tl []     = []
  tl (_:ys) = ys

-- in subtyping it is used with Type' instead of Type.
-- TODO: Figure out which one to use (Type' vs Type) and how
-- to deal with annotations: subst them too or keep them?
-- Subst them!
subst :: Type a Poly -> Name -> Type a Poly -> Type a Poly
subst x forY (A a inTy) = 
  case inTy of
    TFree y | y == forY -> x

    TExists x -> error $ "Should never encounter existentials in subst"

    t1 `TApp` t2 -> A a $ subst x forY t1 `TApp` subst x forY t2
    
    t1 :->: t2 -> A a $ subst x forY t1 :->: subst x forY t2
    
    -- TODO: Fix capture problems here
    Forall x' t -> A a $ Forall x' (subst x forY t)

instL = undefined
instR = undefined