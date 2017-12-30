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
{-# LANGUAGE BangPatterns #-}

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
import Data.Char (isUpper, isLower)
import qualified Data.Map.Strict as M

import CloFRP.AST.Name
import CloFRP.Check.Contexts -- TODO: remove this dependency somehow, or move it so there is no deps between Eval and Check
import CloFRP.Annotated
import CloFRP.Eval.EvalM
import CloFRP.Eval.Value
import CloFRP.Pretty
import CloFRP.Check.Prog
import CloFRP.AST.Helpers
import CloFRP.Check.TypingM

import qualified CloFRP.AST.Prim as P
import           CloFRP.AST (Expr, Prog, Pat, PolyType, Datatype(..))
import qualified CloFRP.AST as E

runtimeErr :: String -> Value a
runtimeErr = Prim . RuntimeErr

globalLookup :: Pretty a => Name -> EvalM a (Maybe (Value a))
globalLookup nm = do
  globals <- getGlobals
  case M.lookup nm globals of
    Nothing -> pure Nothing
    Just v -> pure . Just $ v
    
lookupVar :: Pretty a => Name -> EvalM a (Value a)
lookupVar nm = do
  inEnv <- envLookup nm <$> getEnv 
  inGlob <- globalLookup nm 
  case (inEnv <|> inGlob) of
    Just v -> pure v
    Nothing -> do 
      env <- getEnv
      pure . runtimeErr $ show $ "Cannot lookup" <+> pretty nm <+> "in env" <+> pretty env


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

fmapFromType :: Pretty a => PolyType a -> EvalM a (Value a)
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
  -- we cannot use Haskells let x = f x trick since our let-bindings are eager
  -- and not lazy

  -- if f = (\g -> 0 : (\\af -> map (+1) (g [af]))) then
  -- fix f
  -- => f (\\af. fix f)
  -- => 0 : (\\af -> map (+1) (fix f))
  -- =*> 0 : (map (+1) (fix f))
  P.Fix              -> do
    let delay = tAbs "#alpha" "#clock"
    pure $ Closure mempty "#f" $ var "#f" `app` (delay $ fixE `app` var "#f")
  P.Undefined        -> pure . runtimeErr $ "Undefined!"

evalPrimRec :: (Pretty a, ?annotation :: a) => PolyType a -> EvalM a (Value a)
evalPrimRec t = do
  let (oname, ovar) = (UName "__outer__", var oname)
  let (iname, ivar) = (UName "__inner__", var iname)
  let (bdnm, bdvar) = (UName "__body__", var bdnm)

  let conte = (primRec t `app` bdvar) `app` ivar
  let etup = tuple [ivar, conte]
  let fmaplam = lam' iname etup
  let fmape = (fmapE t `app` fmaplam) `app` (unfoldE `app` ovar)
  evalExprStep $ lam' bdnm $ lam' oname $ bdvar `app` fmape

evalExprStep :: Pretty a => Expr a -> EvalM a (Value a)
evalExprStep (A ann expr') = 
  let ?annotation = ann
  in  case expr' of
    E.Prim !p       -> evalPrim p
    E.TickVar !nm   -> pure $ TickVar nm
    E.Lam x _mty !e -> (\env -> Closure env x e) <$> getEnv
    E.Fmap t        -> fmapFromType t
    E.PrimRec t     -> evalPrimRec t
    E.Ann e _t      -> evalExprStep e
    E.Tuple ts      -> Tuple <$> sequence (map evalExprStep ts) 
    E.Case e1 cs    -> evalExprStep e1 >>= (\v1 -> evalClauses v1 cs)
    E.TypeApp e _t  -> evalExprStep e

    E.Var (E.UName s) | isUpper (head s) -> pure $ Constr (E.UName s) []
    E.Var !nm -> lookupVar nm

    -- E.TickAbs (UName "#alpha") _k !e -> do
    --   Just f <- envLookup "#f" <$> getEnv
    --   pure (TickClosure (singleEnv "#f" f) "#alpha" e)

    E.TickAbs x _k !e -> do
      env <- getEnv
      -- pntr <- allocThunk env x e
      -- pure (Prim (Pointer pntr))
      -- trace ("closing over " ++ pps env) $ 
      pure (TickClosure env x e)

    E.BinOp nm e1 e2 ->
      case nm of
        "+" -> do 
          Prim (IntVal i1) <- evalExprStep e1
          Prim (IntVal i2) <- evalExprStep e2
          pure (Prim (IntVal (i1 + i2)))
        "<" -> do 
          Prim (IntVal i1) <- evalExprStep e1
          Prim (IntVal i2) <- evalExprStep e2
          let c = if (i1 < i2)
                  then "True"
                  else "False"
          pure (Constr c [])
          
        _ -> pure $ runtimeErr ("binary operator " ++ show nm ++ " is not supported")

    {-
    E |- (\body outer -> body (fmap_F (\inner -> <inner, primRec_F body inner>) outer)) \\ v
    ---------------
    E |- primRec_F \\ v

    primRec body x
    => body (fmap (\x -> (x, primRec body x)) x) 

    primRec body
    => \x -> body (fmap (\x -> (x, primRec body x)) x)
    -}
      
    E.App e1 e2 -> do
      !v1 <- evalExprStep e1
      !v2 <- evalExprStep e2
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
            _      -> pure . runtimeErr $ show $ "Cannot unfold" <+> pretty v2 <+> "at" <+> pretty ann
        
        (Delay v, Prim Tick) -> pure v
        (Delay v, TickVar _) -> pure v
        (Prim (RuntimeErr _), _) -> pure v1
        (_, Prim (RuntimeErr _)) -> pure v2

        _ -> pure . runtimeErr $ show $  pretty v1 <+> pretty v2 <+> "is not a legal application at" <+> pretty ann


    E.Let p e1 e2 -> do
      v1 <- evalExprStep e1
      envE' <- evalPat p v1
      case envE' of
        Right env' -> withEnv (const env') $ evalExprStep e2
        Left err -> pure . runtimeErr $ "Let match failed: " ++ err
    


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
-- evalExprCorec :: Pretty a => Expr a -> EvalM a (Value a)
-- evalExprCorec expr = go (1000000 :: Int) =<< evalExprStep expr where 
--   go n v | n <= 0 = pure (runtimeErr $ "Evaluation limit reached")
--   go n v = do
--     case v of
--       Constr nm vs -> Constr nm <$> evalMany n vs
--       Fold v' -> Fold <$> go n v'
--       Tuple vs -> Tuple <$> evalMany n vs
--       _ -> pure v

--   evalMany _ [] = pure []
--   evalMany n (v:vs) = do 
--     v' <- go (n-1) =<< force v
--     (v' :) <$> evalMany (n-1) vs

evalExprCorec :: Pretty a => Expr a -> EvalM a (Value a)
evalExprCorec expr = go =<< evalExprStep expr where 
  go v = do
    case v of
      Constr nm vs -> Constr nm <$> evalMany vs
      Fold v' -> Fold <$> go v'
      Tuple vs -> Tuple <$> evalMany vs
      _ -> pure v

  evalMany = foldrM folder [] where
    folder v acc = do
      (:acc) <$> (go =<< force v)
      
  -- evalMany [] = pure []
  -- evalMany (v:vs) = do 
  --   v' <- go =<< force v
  --   (v' :) <$> evalMany vs

evalStepDefinitions :: Pretty a => EvalRead a -> UsageGraph -> Defs a -> Name -> TypingM a (EvalRead a)
evalStepDefinitions er ug defs defnm = do
  order <- either (tyExcept . Decorate (Other "during evalStepDefinitions")) pure $ usageClosure ug defnm
  -- filter out constructors and main definition
  let orderNoConstrs = [nm | nm <- order, isLower . head . show $ nm, nm /= defnm] 
  foldrM folder er orderNoConstrs where
    folder nm acc = do
      expr <- maybe (otherErr $ show nm ++ " not found") pure $ M.lookup nm defs
      let val = runEvalM (evalExprStep expr) acc 
      pure (acc { erGlobals = extendGlobals nm val (erGlobals acc) })


progToEval :: Pretty a => Name -> Prog a -> TypingM a (Expr a, PolyType a, EvalRead a)
progToEval mainnm pr = do
  let (ElabRes {erDefs, erConstrs, erSigs}) = collectDecls pr
      vconstrs = M.mapWithKey (\k _ -> Right (Constr k [])) . unFreeCtx $ erConstrs
      -- initSt = initEvalState { esGlobals = (M.map Left erDefs) `M.union` vconstrs }
  ElabProg {instances} <- elabProg pr
  let ug = usageGraph erDefs `M.union` constrsToUsageGraph erConstrs
  -- OK, the below should not be here, but when you actually evaluate the program.
  -- right now, evalStepDefinitions evaluates all top-level decls at compile-time
  initRd <- evalStepDefinitions (mempty { erInstances = instances }) ug erDefs mainnm
  case M.lookup mainnm erDefs of 
    Just maindef -> 
      let Just mainty = query mainnm erSigs
      in  pure (maindef, mainty, initRd)
    Nothing -> otherErr $ "No main definition of name " ++ pps mainnm ++ " found"

evalProg :: Pretty a => Name -> Prog a -> Value a
evalProg mainnm pr =
  case runTypingM0 (progToEval mainnm pr) mempty of
    (Right (expr, _ty, er), _, _) -> runEvalM (evalExprCorec expr) er
    (Left (err, _), _, _)         -> runtimeErr (pps err)

