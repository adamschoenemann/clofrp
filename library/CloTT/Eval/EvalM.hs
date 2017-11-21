{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CloTT.Eval.EvalM where

import Control.Monad.RWS.Lazy hiding ((<>))
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State ()
import Data.Text.Prettyprint.Doc 
import Control.Applicative
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import CloTT.Eval.Value
import CloTT.AST.Name
import qualified CloTT.AST.Expr as E
import CloTT.AST.Expr (Expr)

type EvalRead a = Env a
type EvalWrite = ()
type Globals a = Map Name (Either (Expr a) (Value a)) -- either unevaled defs or already evaled values
type EvalState a = Globals a

data EvalErr = Other String
  deriving (Show, Eq)

newtype EvalM a r = Eval { unEvalM :: RWS (EvalRead a) EvalWrite (EvalState a) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState  (EvalState a)
           , MonadWriter EvalWrite 
           , MonadReader (EvalRead a)
           )

type EvalMRes r = r

-- instance Alternative (EvalM a) where 
--   empty = otherErr "Alternative.empty for EvalM"
--   x <|> y = x `catchError` \e -> y


runEvalM :: EvalM a r -> (EvalRead a) -> EvalMRes r
-- runEvalM tm r = let x = runRWS (unEvalM tm) r in x
runEvalM tm r = let (x, _, _) = runRWS (unEvalM tm) r mempty in x

getEnv :: EvalM a (Env a)
getEnv = ask

withEnv :: (EvalRead a -> EvalRead a) -> EvalM a r -> EvalM a r
withEnv = local

updGlobals :: (EvalState a -> EvalState a) -> EvalM a ()

updGlobals = modify

getGlobals :: EvalM a (Globals a)
getGlobals = get

otherErr :: String -> EvalM a (Value a)
otherErr = pure . Prim . RuntimeErr 