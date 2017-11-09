{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

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
import qualified Data.Map.Strict as M

import CloTT.AST.Name
import CloTT.Check.Contexts -- TODO: remove this dependency somehow, or move it so there is no deps between Eval and Check
import CloTT.Annotated
import CloTT.Eval.EvalM
import CloTT.Eval.Value
import CloTT.Pretty
import CloTT.Check.Prog

import qualified CloTT.AST.Prim as P
import           CloTT.AST.Parsed (Expr, Prog, Pat)
import qualified CloTT.AST.Parsed as E

globalLookup :: Name -> EvalM a (Maybe (Value a))
globalLookup nm = do
  globals <- getGlobals
  case M.lookup nm globals of
    Nothing -> pure Nothing
    Just (Right v) -> pure . Just $ v
    Just (Left e) -> Just <$> evalExprStep e
    


lookupVar :: Name -> EvalM a (Value a)
lookupVar nm = do
  inEnv <- envLookup nm <$> getEnv 
  inGlob <- globalLookup nm 
  case (inEnv <|> inGlob) of
    Just v -> pure v
    Nothing -> do 
      env <- getEnv
      otherErr $ show $ "Cannot lookup" <+> pretty nm <+> "in env" <+> pretty env

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
        Constr nm' vs 
          | nm == nm' -> do 
              env <- getEnv
              foldrM folder (Right env) (zip ps vs) 
          | otherwise -> pure $ Left $ show $ "Constructor pattern failed: expected" <+> pretty nm <+> "but got" <+> pretty nm'
        _        -> pure $ Left $ "Constructor pattern failed:"
      where
        folder (p', v') (Right acc) = withEnv (const acc) $ evalPat p' v'
        folder _  (Left err)  = pure (Left err)

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
        Left err -> pure . Prim . RuntimeErr $ "Let match failed: " ++ err
    
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

force :: Value a -> EvalM a (Value a)
force = \case
  TickClosure cenv nm e -> 
    withEnv (\e -> combine e (extend nm (Prim Tick) cenv)) $ evalExprStep e
  v -> pure v

evalExprCorec :: Expr a -> EvalM a (Value a)
evalExprCorec expr = go (1000000 :: Int) =<< evalExprStep expr where 
  go n v | n <= 0 = pure v
  go n v = do
    case v of
      Constr nm vs -> Constr nm <$> evalMany n vs
      _ -> pure v

  evalMany _ [] = pure []
  evalMany n (v:vs) = do 
    v' <- go (n-1) =<< force v
    vs' <- evalMany (n-1) vs
    pure (v' : vs')

evalProg :: Name -> Prog a -> Value a
evalProg mainnm pr =
  let er@(ElabRes {erDefs, erConstrs}) = collectDecls pr
      vconstrs = M.mapWithKey (\k v -> Right (Constr k [])) . unFreeCtx $ erConstrs
      initState = (M.map Left erDefs) `M.union` vconstrs
  in  case M.lookup mainnm erDefs of 
        Just maindef -> 
          runEvalM (updGlobals (const initState) >> evalExprCorec maindef) mempty
        Nothing -> Prim . RuntimeErr $ "No main definition of name " ++ pps mainnm ++ " found"