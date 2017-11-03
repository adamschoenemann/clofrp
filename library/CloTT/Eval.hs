{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}

module CloTT.Eval where

import Control.Monad.RWS.Strict hiding ((<>))
import Control.Monad.Except
import Control.Monad.State ()
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import CloTT.AST.Name
import qualified CloTT.AST.Prim as P

-- |A Value is an expression that is evaluated to normal form
data Value
  = Prim (P.Prim)
  | Closure Env Name Value
  deriving (Show, Eq)

type Env = Map Name Value

type EvalRead = Env
type EvalWrite = ()
type EvalState = ()

data EvalErr = Other String

newtype EvalM a r = Eval { unEvalM :: ExceptT EvalErr (RWS EvalRead EvalWrite EvalState) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError  EvalErr 
           , MonadState  EvalState
           , MonadWriter EvalWrite 
           , MonadReader EvalRead
           )

type EvalMRes r = Either EvalErr r

runEvalM :: EvalM a r -> EvalRead -> EvalMRes r
runEvalM tm r = let (x, _, _) = runRWS (runExceptT (unEvalM tm)) r () in x