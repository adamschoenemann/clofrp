{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module CloTT.Eval 
  ( module CloTT.Eval.EvalM
  , module CloTT.Eval.Value
  , module CloTT.Eval
  ) where

import Data.Text.Prettyprint.Doc 
import Control.Applicative ((<|>))
import Data.Foldable (foldrM, foldlM)
import Control.Monad ((<=<))
import Debug.Trace
import Control.Monad.Reader
import Control.Monad.Except
import Data.Either

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.Eval.EvalM
import CloTT.Eval.Value
import CloTT.Pretty

import qualified CloTT.AST.Prim as P
import           CloTT.AST.Expr (Expr)
import qualified CloTT.AST.Expr as E
import           CloTT.AST.Pat (Pat)
import qualified CloTT.AST.Pat  as E

evalPat :: Pat a -> Value a -> EvalM a (Either String (Env a))
evalPat (A _ p) v =
  case p of
    E.Bind nm -> Right <$> extend nm v <$> getEnv
    E.PTuple ps -> 
      case v of
        Tuple vs -> do 
          env <- getEnv
          foldr folder (pure $ Right env) $ zip ps vs
          where
            folder (p', v') m = m >>= \case
              Left err -> pure $ Left err
              Right env -> withEnv (const env) $ evalPat p' v'
          
        _        -> pure $ Left $ "Tuple pattern failed"
    E.Match nm ps ->
      case v of 
        Constr nm' vs | nm == nm' -> do 
          env <- getEnv
          foldrM folder (Right env) (zip ps vs) 
          where
            folder (p', v') (Right acc) = withEnv (const acc) $ evalPat p' v'
            folder _  (Left err)  = pure (Left err)
        _        -> pure $ Left $ "Constructor pattern failed"

evalClauses :: Value a -> [(Pat a, Expr a)] -> EvalM a (Value a)
evalClauses val [] = pure . Prim . RuntimeErr $ "No clause matched"
evalClauses val (c : cs) = 
  evalClause val c >>= \case 
    Right v -> pure v
    Left  e -> evalClauses val cs

evalClause :: Value a -> (Pat a, Expr a) -> EvalM a (Either String (Value a))
evalClause val (p, e) = do
  envE <- evalPat p val
  case envE of
    Right env' -> Right <$> (withEnv (const env') $ evalExprStep e)
    Left err -> pure $ Left err

evalPrim :: P.Prim -> EvalM a (Value a)
evalPrim = \case
  P.Unit             -> pure $ Constr "Unit" []
  P.Integer i        -> pure . Prim . IntVal $ i
  P.Fold             -> pure . Prim $ Fold
  P.Unfold           -> pure . Prim $ Unfold
  P.PrimRec          -> pure . Prim $ PrimRec
  P.Tick             -> pure . Prim $ Tick
  P.Fix              -> pure . Prim $ Fix
  P.Undefined        -> otherErr $ "Undefined!"

evalExprStep :: Expr a -> EvalM a (Value a)
evalExprStep (A ann expr') = 
  case expr' of
    E.Prim p -> evalPrim p
    E.Var nm -> lookupVar nm
    
    E.TickVar nm -> pure $ TickVar nm

    E.Lam x _mty e -> do
      env <- getEnv
      pure (Closure env x e)

    E.TickAbs x k e -> do
      env <- getEnv
      pure (TickClosure env x e)
    
    E.App e1 e2 -> do
      v1 <- evalExprStep e1
      v2 <- evalExprStep e2
      case (v1, v2) of 
        -- order of union of envs is very important to avoid incorrect name capture
        (Closure cenv nm e1', _) -> do
          let cenv' = extend nm v2 cenv
          withEnv (combine cenv') $ evalExprStep e1'

        (TickClosure cenv nm e1', _) -> do
          let cenv' = extend nm v2 cenv
          withEnv (combine cenv') $ evalExprStep e1'

        (Constr nm args, _) -> do
          pure $ Constr nm (args ++ [v2])
        
        (Prim Unfold, _) -> pure v2
        (Prim Fold, _)   -> pure v2

        -- fix f ~> f (dfix f)
        -- fix f ~> f (\\(af). fix f)

        --    f =>σ (\x. e1', σ')       e1' =>(σ, x ↦ \\af. fix f, σ') v
        --  ----------------------------------------------------------------
        --                      fix f =>σ v
        (Prim Fix, Closure cenv nm e2') -> do
          let app x y = A ann $ x `E.App` y
          let fixe = A ann $ E.Prim P.Fix
          env <- getEnv
          let cenv' = extend nm (TickClosure env (DeBruijn 0) $ fixe `app` e2) cenv
          withEnv (combine cenv') $ evalExprStep e2'

        _ -> otherErr $ show $ "Expected" <+> pretty v1 <+> "to be a lambda or something"
    
    E.Ann e t -> evalExprStep e

    E.Tuple ts -> Tuple <$> sequence (map evalExprStep ts) 

    E.Let p e1 e2 -> do
      v1 <- evalExprStep e1
      envE' <- evalPat p v1
      case envE' of
        Right env' -> withEnv (const env') $ evalExprStep e2
        Left err -> pure . Prim . RuntimeErr $ "Let match failed"
    
    E.Case e1 cs -> do
      v1 <- evalExprStep e1
      evalClauses v1 cs

    E.TypeApp e t -> evalExprStep e


-- proof that the except monad is not lazy
type TestM a = ReaderT () (Except ()) a

coindplz :: [()]
coindplz = let Right x = runTestM loop in x where
  loop :: TestM [()]
  loop = do
    l <- loop
    pure (() : l)
  
  runTestM :: TestM r -> Either () r
  runTestM x = runExcept (runReaderT x ())

evalExprUntil :: Expr a -> EvalM a (Value a)
evalExprUntil expr = check (100 :: Int) expr where 
  check n e | n <= 0 = evalExprStep e
  check n e = do
    v <- evalExprStep e
    case v of
      Constr nm vs -> Constr nm <$> evalMany n vs
      _ -> pure v

  evalMany _ [] = pure []
  evalMany n (TickClosure env nm e : vs) = do 
    v' <- withEnv (\e -> combine e (extend nm (Prim Tick) env)) $ check n e
    vs' <- evalMany (n-1) vs
    pure (v' : vs')
  evalMany n (v:vs) = (v :) <$> evalMany (n-1) vs