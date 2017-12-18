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

module CloFRP.Eval 
  ( module CloFRP.Eval.EvalM
  , module CloFRP.Eval.Value
  , module CloFRP.Eval
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

import CloFRP.AST.Name
import CloFRP.Check.Contexts -- TODO: remove this dependency somehow, or move it so there is no deps between Eval and Check
import CloFRP.Annotated
import CloFRP.Eval.EvalM
import CloFRP.Eval.Value
import CloFRP.Pretty
import CloFRP.Check.Prog
import CloFRP.AST.Helpers

import qualified CloFRP.AST.Prim as P
import           CloFRP.AST (Expr, Prog, Pat, Type, TySort(..), Datatype(..))
import qualified CloFRP.AST as E

runtimeErr :: String -> Value a
runtimeErr = Prim . RuntimeErr

globalLookup :: Pretty a => Name -> EvalM a (Maybe (Value a))
globalLookup nm = do
  globals <- getGlobals
  case M.lookup nm globals of
    Nothing -> pure Nothing
    Just (Right v) -> pure . Just $ v
    Just (Left e) -> Just <$> evalExprStep e
    
lookupVar :: Pretty a => Name -> EvalM a (Value a)
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

fmapFromType :: Pretty a => Type a 'Poly -> EvalM a (Value a)
fmapFromType ty = findInstanceOf "Functor" ty >>= \case
  Just (ClassInstance {ciDictionary = dict}) -> 
    maybe (pure $ runtimeErr "Functor without fmap!!") (evalExprStep . snd) (M.lookup "fmap" dict)

  Nothing -> pure $ runtimeErr $ show $ "No functor instance for" <+> pretty ty


-- lookupFmap :: a -> Value a -> EvalM a (Expr a)
-- lookupFmap ann (Constr "Z" _) = pure $ fmapNat ann
-- lookupFmap ann (Constr "S" _) = pure $ fmapNat ann
-- lookupFmap _ _                = error "lookupFmap"

-- getFmap :: Value a -> Value a -> EvalM (Value a)
-- getFmap f = \case
--   Constr nm cstrs -> do
--     fm <- lookupFmap nm

evalPat :: Pat a -> Value a -> EvalM a (Either String (Env a))
evalPat pat@(A _ p) v =
  case p of
    E.Bind nm -> Right <$> extendEnv nm v <$> getEnv
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
        _        -> pure $ Left $ show $ "Constructor pattern failed: pattern was" <+> pretty pat <+> "but got value" <+> pretty v
      where
        folder (p', v') (Right acc) = withEnv (const acc) $ evalPat p' v'
        folder _  (Left err)  = pure (Left err)

evalClauses :: Pretty a => Value a -> [(Pat a, Expr a)] -> EvalM a (Value a)
evalClauses (Prim (RuntimeErr e)) _ = pure (runtimeErr e)
evalClauses value clauses = helper value clauses where
  helper val [] = 
    let pcls = indent 4 $ vsep $ map (\(a,b) -> group (pretty a) <+> "->" <+> pretty b) clauses
    in  pure . runtimeErr $ show $ "None of the clauses" <> line <> pcls <+> "matched" <+> pretty val
  helper val (c : cs) = 
    evalClause val c >>= \case 
      Right v -> pure v
      Left  e -> helper val cs

evalClause :: Pretty a => Value a -> (Pat a, Expr a) -> EvalM a (Either String (Value a))
evalClause val (p, e) = do
  envE <- evalPat p val
  case envE of
    Right env' -> Right <$> (withEnv (const env') $ evalExprStep e)
    Left err -> pure $ Left err

evalPrim :: (Pretty a, ?annotation :: a) => P.Prim -> EvalM a (Value a)
evalPrim = \case
  P.Unit             -> pure $ Constr "Unit" []
  P.Integer i        -> pure . Prim . IntVal $ i
  P.Fold             -> pure . Prim $ FoldP
  P.Unfold           -> pure . Prim $ UnfoldP
  P.Tick             -> pure . Prim $ Tick
  P.Input            -> getInput

  -- fix ~> \f -> f (dfix f)
  -- fix ~> \f -> f (\\(af). fix f)
  P.Fix              -> 
    pure $ Closure mempty "#f" $ var "#f" `app` (tAbs "#alpha" "#clock" $ fixE `app` var "#f")
  P.Undefined        -> otherErr $ "Undefined!"

evalExprStep :: Pretty a => Expr a -> EvalM a (Value a)
evalExprStep (A ann expr') = 
  let ?annotation = ann
  in  case expr' of
    E.Prim p -> evalPrim p
    E.Var nm -> lookupVar nm
    
    E.TickVar nm -> pure $ TickVar nm

    E.Lam x _mty e -> do
      env <- getEnv
      pure (Closure env x e)

    E.TickAbs x _k e -> do
      env <- getEnv
      pure (TickClosure env x e)
    
    E.Fmap t -> fmapFromType t

    {-
    E |- (\body outer -> body (fmap_F (\inner -> <inner, primRec_F body inner>) outer)) \\ v
    ---------------
    E |- primRec_F \\ v

    primRec body x
    => body (fmap (\x -> (x, primRec body x)) x) 

    primRec body
    => \x -> body (fmap (\x -> (x, primRec body x)) x)
    -}
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
      let fmape = (fmapE t `app` fmaplam) `app` (unfoldE `app` ovar)
      evalExprStep $ lam' bdnm $ lam' oname $ bdvar `app` fmape
      
    E.App e1 e2 -> do
      v1 <- evalExprStep e1
      v2 <- evalExprStep e2
      case (v1, v2) of 
        (Closure cenv nm e1', _) -> do
          let cenv' = extendEnv nm v2 cenv
          withEnv (const cenv') $ evalExprStep e1'

        (TickClosure cenv nm e1', _) -> do
          let cenv' = extendEnv nm v2 cenv
          withEnv (const cenv') $ evalExprStep e1'

        (Constr nm args, _) -> do
          pure $ Constr nm (args ++ [v2])
        
        (Prim FoldP, _) -> pure $ Fold v2
        (Prim UnfoldP, _) -> 
          case v2 of 
            Fold v -> pure v
            _      -> otherErr $ show $ "Cannot unfold" <+> pretty v2 <+> "at" <+> pretty ann
        
        (Delay v, Prim Tick) -> pure v
        (Delay v, TickVar _) -> pure v
        (Prim (RuntimeErr _), _) -> pure v1
        (_, Prim (RuntimeErr _)) -> pure v2

        _ -> otherErr $ show $  pretty v1 <+> pretty v2 <+> "is not a legal application at" <+> pretty ann

    E.Ann e _t -> evalExprStep e

    E.Tuple ts -> Tuple <$> sequence (map evalExprStep ts) 

    E.Let p e1 e2 -> do
      v1 <- evalExprStep e1
      envE' <- evalPat p v1
      case envE' of
        Right env' -> withEnv (const env') $ evalExprStep e2
        Left err -> pure . runtimeErr $ "Let match failed: " ++ err
    
    E.Case e1 cs -> do
      v1 <- evalExprStep e1
      evalClauses v1 cs

    E.TypeApp e _t -> evalExprStep e


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

force :: Pretty a => Value a -> EvalM a (Value a)
force = \case
  TickClosure cenv nm expr -> 
    withEnv (const $ extendEnv nm (Prim Tick) cenv) $ evalExprStep expr
  Delay v -> pure v
  v -> pure v

{- evalExprCorec (fix (\g -> cons z g))
  => Constr "Cons" [Constr "Z" [], TickClosure _ _ e]
  => Constr "Cons" [Constr "Z" [], Constr "Cons" [Constr "Z", TickClosure _ _ e]]
-}
evalExprCorec :: Pretty a => Expr a -> EvalM a (Value a)
evalExprCorec expr = go (1000000 :: Int) =<< evalExprStep expr where 
  go n v | n <= 0 = pure v
  go n v = do
    case v of
      Constr nm vs -> Constr nm <$> evalMany n vs
      Fold v -> Fold <$> go n v
      Tuple vs -> Tuple <$> evalMany n vs
      _ -> pure v

  evalMany _ [] = pure []
  evalMany n (v:vs) = do 
    v' <- go (n-1) =<< force v
    vs' <- evalMany (n-1) vs
    pure (v' : vs')


progToEval :: Name -> Prog a -> Either String (Expr a, Type a 'Poly, EvalRead a, EvalState a)
progToEval mainnm pr = do
  let er@(ElabRes {erDefs, erConstrs, erDeriving, erSigs}) = collectDecls pr
      vconstrs = M.mapWithKey (\k v -> Right (Constr k [])) . unFreeCtx $ erConstrs
      initState = (M.map Left erDefs) `M.union` vconstrs
  instances <- elabInstances id erDeriving
  let initRead = mempty { erInstances = instances }
  case M.lookup mainnm erDefs of 
    Just maindef -> 
      let Just mainty = query mainnm erSigs
      in  Right (maindef, mainty, initRead, initState)
    Nothing -> Left $ "No main definition of name " ++ pps mainnm ++ " found"

evalProg :: Pretty a => Name -> Prog a -> Value a
evalProg mainnm pr =
  case progToEval mainnm pr of
    Right (expr, _ty, er, es) -> runEvalMState (evalExprCorec expr) er es
    Left err                  -> runtimeErr err

