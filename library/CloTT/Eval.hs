{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import CloTT.AST.Helpers

import qualified CloTT.AST.Prim as P
import           CloTT.AST.Parsed (Expr, Prog, Pat, Type, TySort(..), Datatype(..))
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


fmapNat :: a -> Expr a
fmapNat ann = 
  let ?annotation = ann in
  let fn = UName "__fn__"
      ftornm = UName "__ftor__"
      ftor = var ftornm
      f = var fn
      s = var "S"
  in lam fn Nothing (lam ftornm Nothing $ casee ftor 
      [ (match "Z" [], var "Z")
      , (match "S" [bind (UName "_n")], s `app` (f `app` var "_n"))
      ]
     ) 

fmapFromType :: Type a Poly -> EvalM a (Expr a)
fmapFromType (A ann ty) =
  case ty of
    E.TFree "NatF" -> pure $ fmapNat ann
    _     -> error "fmapFromType"

lookupFmap :: a -> Value a -> EvalM a (Expr a)
lookupFmap ann (Constr "Z" _) = pure $ fmapNat ann
lookupFmap ann (Constr "S" _) = pure $ fmapNat ann
lookupFmap _ _             = error "lookupFmap"

-- getFmap :: Value a -> Value a -> EvalM (Value a)
-- getFmap f = \case
--   Constr nm cstrs -> do
--     fm <- lookupFmap nm

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
evalClauses (Prim (RuntimeErr e)) _ = pure (Prim $ RuntimeErr e)
evalClauses value clauses = helper value clauses where
  helper val [] = 
    let pcls = indent 4 $ vsep $ map (\(a,b) -> group (pretty a) <+> "->" <+> pretty b) clauses
    in  pure . Prim . RuntimeErr $ show $ "None of the clauses" <> line <> pcls <+> "matched" <+> pretty val
  helper val (c : cs) = 
    evalClause val c >>= \case 
      Right v -> pure v
      Left  e -> helper val cs

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
  P.Tick             -> pure . Prim $ Tick
  P.Fix              -> pure . Prim $ Fix
  P.Undefined        -> otherErr $ "Undefined!"

evalExprStep :: Expr a -> EvalM a (Value a)
evalExprStep (A ann expr') = 
  let ?annotation = ann
  in  case expr' of
    E.Prim p -> evalPrim p
    E.Var nm -> lookupVar nm
    
    E.TickVar nm -> pure $ TickVar nm

    E.Lam x _mty e -> do
      env <- getEnv
      pure (Closure env x e)

    E.TickAbs x k e -> do
      env <- getEnv
      pure (TickClosure env x e)
    
    E.Fmap t -> evalExprStep =<< fmapFromType t
    E.PrimRec t -> do
      let oname = UName "__outer__"
      let ovar = var oname
      let iname = UName "__inner__"
      let ivar = var iname
      let bdnm = UName "__body__"
      let bdvar = var bdnm

      let conte = (primRec t `app` bdvar) `app` ivar
      let etup = tuple [ivar, conte]
      let fmaplam = lam iname Nothing etup
      let fmape = (fmapE t `app` fmaplam) `app` ovar
      evalExprStep $ lam' bdnm $ lam' oname $ bdvar `app` fmape
      
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
          let fixe = prim P.Fix
          env <- getEnv
          let cenv' = extend nm (TickClosure env (DeBruijn 0) $ fixe `app` e2) cenv
          withEnv (combine cenv') $ evalExprStep e2'
        
        -- (GetFmap f, v) -> do
        --   fm <- lookupFmap ann v
        --   evalExprStep ((fm `app` f `app`) e2)
        
        {-
        primRec body x
        => body (fmap (\x -> (x, primRec body x)) x) 

        primRec body
        => \x -> body (fmap (\x -> (x, primRec body x)) x)
        -}
        -- (Prim PrimRec, _) -> do
        --   let oname = UName "__outer__"
        --   let ovar = var oname
        --   let iname = UName "__inner__"
        --   let ivar = var iname

        --   let conte = (prim P.PrimRec `app` e2) `app` ivar
        --   let etup = tuple [ivar, conte]
        --   let fmaplam = lam iname Nothing etup
        --   let fmape = (prim E.Fmap `app` fmaplam) `app` ovar
        --   let bdeapp = e2 `app` fmape 
        --   env <- getEnv
        --   let r = Closure env oname bdeapp
        --   pure $ r
        
        (Prim (RuntimeErr _), _) -> pure v1
        (_, Prim( RuntimeErr _)) -> pure v2

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

