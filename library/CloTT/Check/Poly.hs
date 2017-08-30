{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module CloTT.Check.Poly where

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.AST.Parsed
import Control.Monad.RWS.Strict
import Control.Monad.Except

data CtxElem a
  = Uni Name
  | Exists Name
  | Name `HasType` Type a Poly
  | Name `Assigned` Type a Mono
  | Marker Name
  deriving (Show, Eq)

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

-- just an integer for generating names
type TypingState  = Integer
type TypingRead a = TyCtx a

data TyExcept 
  = Other String
  deriving (Show, Eq)

-- the typing monad
newtype TypingM a r = TypingM { unTypingM :: RWST (TypingRead a) () TypingState (Except TyExcept) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError TyExcept
           , MonadState TypingState
           , MonadWriter ()
           , MonadReader (TypingRead a)
           )

subtypeOf :: Eq a => Type a Poly -> Type a Poly -> TypingM a (TyCtx a)
subtypeOf (A _ t1) (A _ t2) = subtypeOf' t1 t2 where
  subtypeOf' :: Eq a => Type' a Poly -> Type' a Poly -> TypingM a (TyCtx a)
  subtypeOf' (TFree a) (TFree a')
    | a == a'    = ask
    | otherwise = throwError $ Other $ show a ++ " does not subtype " ++ show a'
  
  subtypeOf' (a1 :->: a2) (b1 :->: b2) = do
    ctx' <- b1 `subtypeOf` a1
    local (const ctx') $ (substCtx ctx' a2) `subtypeOf'` (substCtx ctx' b2)

substCtx = undefined