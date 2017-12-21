{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CloFRP.Eval.EvalM where

import Control.Monad.RWS.Lazy hiding ((<>))
import Control.Monad.State ()
import Data.Map.Strict (Map)
import qualified Data.Map.Lazy as M
import Data.Data

import CloFRP.Eval.Value
import CloFRP.AST.Name
import qualified CloFRP.AST.Expr as E
import CloFRP.AST.Expr (Expr)
import CloFRP.Check.Contexts (InstanceCtx(..), HasInstances(..))
import CloFRP.AST.Prim (Pntr)

type Inputs a = Map Name (Value a)

data EvalRead a = 
  EvalRead { erEnv :: Env a, erInstances :: InstanceCtx a, erInputs :: Inputs a }
  deriving (Show, Eq, Typeable, Data)

instance Monoid (EvalRead a) where
  mempty = EvalRead mempty mempty mempty
  er1 `mappend` er2 = 
    EvalRead { erEnv       = erEnv er1 `mappend` erEnv er2 
             , erInstances = erInstances er1 `mappend` erInstances er2 
             , erInputs    = erInputs er1 `mappend` erInputs er2 
             }

type EvalWrite = ()
type Globals a = Map Name (Either (Expr a) (Value a)) -- either unevaled defs or already evaled values
type Thunks a = Map Pntr (Either (Env a, Name, Expr a) (Value a)) 
data EvalState a = 
  ES { esGlobals :: Globals a 
     , esPntrLbl :: Pntr
     , esThunks :: Thunks a
     } deriving (Show, Eq, Typeable, Data)

initEvalState :: EvalState a
initEvalState = ES { esGlobals = mempty, esPntrLbl = 0, esThunks = mempty }

allocThunk :: Env a -> Name -> Expr a -> EvalM a Pntr
allocThunk env nm e = do
  pntr <- getPntr
  modifyThunks (M.insert pntr (Left (env, nm, e)))
  modifyPntr succ
  pure (succ pntr)

newtype EvalM a r = Eval { unEvalM :: RWS (EvalRead a) EvalWrite (EvalState a) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState  (EvalState a)
           , MonadWriter EvalWrite 
           , MonadReader (EvalRead a)
           )

instance HasInstances (EvalM a) a where
  getInstances = asks erInstances

type EvalMRes r = r

runEvalM :: EvalM a r -> EvalRead a -> EvalMRes r
runEvalM tm r = runEvalMState tm r initEvalState

runEvalMState :: EvalM a r -> EvalRead a -> EvalState a -> EvalMRes r
-- runEvalM tm r = let x = runRWS (unEvalM tm) r in x
runEvalMState tm r st = let (x, _, _) = runRWS (unEvalM tm) r st in x

getEnv :: EvalM a (Env a)
getEnv = asks erEnv

getInputs :: EvalM a (Inputs a)
getInputs = asks erInputs

getInput :: EvalM a (Value a)
getInput = do 
  is <- asks erInputs
  case M.lookup "#INPUT" is of
    Just v -> pure v
    Nothing -> pure . Prim $ RuntimeErr "No inputs"

withEnv :: (Env a -> Env a) -> EvalM a r -> EvalM a r
withEnv f = local (\e -> e { erEnv = f (erEnv e) })

withInputs :: (Inputs a -> Inputs a) -> EvalM a r -> EvalM a r
withInputs f = local (\e -> e { erInputs = f (erInputs e) })

withInput :: Value a -> EvalM a r -> EvalM a r
withInput x = withInputs (M.insert "#INPUT" x)

updGlobals :: (EvalState a -> EvalState a) -> EvalM a ()
updGlobals = modify

getGlobals :: EvalM a (Globals a)
getGlobals = gets esGlobals

getThunks :: EvalM a (Thunks a)
getThunks = gets esThunks

modifyThunks :: (Thunks a -> Thunks a) -> EvalM a ()
modifyThunks fn = modify (\es -> es { esThunks = fn (esThunks es) })

modifyPntr :: (Pntr -> Pntr) -> EvalM a ()
modifyPntr fn = modify (\es -> es { esPntrLbl = fn (esPntrLbl es) })

getPntr :: EvalM a Pntr
getPntr = gets esPntrLbl
