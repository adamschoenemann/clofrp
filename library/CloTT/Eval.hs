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
import Data.Text.Prettyprint.Doc 

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.Pretty
import qualified CloTT.AST.Prim as P
import CloTT.AST.Expr (Expr)
import qualified CloTT.AST.Expr as E

-- |A Value is an expression that is evaluated to normal form
data Value a
  = Prim (P.Prim)
  | Var Name
  | Closure (Env a) Name (E.Expr a)
  | Tuple [Value a]
  deriving (Eq)

instance Pretty (Value a) where
  pretty = \case
    Prim p -> pretty p
    Var nm  -> pretty nm
    Closure _ n e -> "λ" <> pretty e <+> "->" <+> pretty e
    Tuple vs -> tupled (map pretty vs)

instance Show (Value a) where
  show = show . pretty

type Env a = Map Name (Value a)

type EvalRead a = Env a
type EvalWrite = ()
type EvalState = ()

data EvalErr = Other String
  deriving (Show, Eq)

newtype EvalM a r = Eval { unEvalM :: ExceptT EvalErr (RWS (EvalRead a) EvalWrite EvalState) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError  EvalErr 
           , MonadState  EvalState
           , MonadWriter EvalWrite 
           , MonadReader (EvalRead a)
           )

type EvalMRes r = Either EvalErr r

runEvalM :: EvalM a r -> (EvalRead a) -> EvalMRes r
runEvalM tm r = let (x, _, _) = runRWS (runExceptT (unEvalM tm)) r () in x

getEnv :: EvalM a (Env a)
getEnv = ask

withEnv :: (EvalRead a -> EvalRead a) -> EvalM a r -> EvalM a r
withEnv = local

evalExpr :: Expr a -> EvalM a (Value a)
evalExpr (A _ expr') = 
  case expr' of
    E.Prim p -> pure (Prim p)
    E.Var nm ->
      M.lookup nm <$> getEnv >>= \case
        Just v -> pure v
        Nothing -> throwError (Other $ "Cannot lookup" ++ show nm)

    E.Lam x _mty e -> do
      env <- getEnv
      pure (Closure env x e)
    
    E.App e1 e2 -> do
      v1 <- evalExpr e1
      case v1 of 
        Closure cenv nm e1' -> do
          v2 <- evalExpr e2
          env <- getEnv
          let env' = M.insert nm v2 env
          withEnv (const (cenv `M.union` env')) $ evalExpr e1'
        _ -> throwError (Other $ "Expected" ++ show v1 ++ "to be a lambda")
    
    E.Ann e t -> evalExpr e

    E.Tuple ts -> Tuple <$> sequence (map evalExpr ts) 

