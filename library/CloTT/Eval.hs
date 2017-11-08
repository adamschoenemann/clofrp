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

import CloTT.AST.Name
import CloTT.Annotated
import CloTT.Eval.EvalM
import CloTT.Eval.Value

import qualified CloTT.AST.Prim as P
import           CloTT.AST.Expr (Expr)
import qualified CloTT.AST.Expr as E
import           CloTT.AST.Pat (Pat)
import qualified CloTT.AST.Pat  as E

evalPat :: Pat a -> Value a -> EvalM a (Env a)
evalPat (A _ p) v =
  case p of
    E.Bind nm -> extend nm v <$> getEnv
    E.PTuple ps -> 
      case v of
        Tuple vs -> combineMany <$> sequence (map (uncurry evalPat) $ zip ps vs)
        _        -> otherErr $ "Tuple pattern failed"
    E.Match nm ps ->
      case v of 
        Constr nm' vs | nm == nm' -> do 
          env <- getEnv
          foldrM folder env (zip ps vs) 
          where
            folder (p', v') acc = withEnv (const acc) $ evalPat p' v'
        _        -> otherErr $ "Constructor pattern failed"

evalClause :: Value a -> (Pat a, Expr a) -> EvalM a (Value a)
evalClause val (p, e) = do
  env' <- evalPat p val
  withEnv (const env') $ evalExprStep e

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
          let env' = extend nm (TickClosure env (DeBruijn 0) $ fixe `app` e2) env
          withEnv (const (env' `combine` cenv)) $ evalExprStep e2'

        _ -> otherErr $ show $ "Expected" <+> pretty v1 <+> "to be a lambda or something"
    
    E.Ann e t -> evalExprStep e

    E.Tuple ts -> Tuple <$> sequence (map evalExprStep ts) 

    E.Let p e1 e2 -> do
      v1 <- evalExprStep e1
      env' <- evalPat p v1
      withEnv (const env') $ evalExprStep e2
    
    E.Case e1 cs -> do
      v1 <- evalExprStep e1
      foldr1 (<|>) $ map (evalClause v1) cs

    E.TypeApp e t -> evalExprStep e

evalExprUntil :: Expr a -> s -> (s -> (Bool, s)) -> EvalM a (Value a)
evalExprUntil expr init p = check init =<< evalExprStep expr where 
  check s v =
    let (b, s') = p s
    in if b 
        then pure v
        else case v of
          Prim p -> pure v
          Var nm  -> lookupVar nm 
          TickVar nm  -> pure v
          Closure env nm e -> pure v
          TickClosure cenv nm e -> do -- force it!
            let cenv' = extend nm (Prim Tick) cenv
            check s' <=< withEnv (combine cenv') $ evalExprUntil e s' p

          Tuple vs -> Tuple <$> sequence (map (check s') vs)
          Constr nm vs -> do
            vs' <- evalMany s' vs
            pure (Constr nm vs')

  evalMany s [] = pure []
  evalMany s (v:vs) = do 
    v' <- check s v
    vs' <- evalMany s vs
    pure (v' : vs')

    

-- evalExprUntil expr init p = check init =<< evalExprStep expr where 
--   check s v =
--     let (b, s') = p (v, s)
--     in if b 
--         then pure v
--         else evalDelayed (check s') v

--   evalDelayed go v = case v of
      -- Prim p -> pure v
      -- Var nm  -> lookupVar nm 
      -- TickVar nm  -> pure v
      -- Closure env nm e -> pure v
      -- TickClosure cenv nm e -> do -- force it!
      --   let cenv' = extend nm (Prim Tick) cenv
      --   go <=< withEnv (combine cenv') $ evalExprStep e

      -- Tuple vs -> Tuple <$> sequence (map go vs)
      -- Constr nm [] -> pure v
      -- Constr nm vs -> do 
      --   vs' <- foldrM folder [] vs
      --   pure (Constr nm vs')
      --   where 
      --     folder x acc = (: acc) <$> go x