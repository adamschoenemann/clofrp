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

import qualified CloTT.AST.Prim as P
import           CloTT.AST.Parsed (Expr, Prog, Pat, Type, TySort(..), Datatype(..))
import qualified CloTT.AST.Parsed as E

-- helper functions here
app :: (?annotation :: a) => Expr a -> Expr a -> Expr a
app x y = A ?annotation $ x `E.App` y

prim :: (?annotation :: a) => E.Prim -> Expr a
prim = A ?annotation . E.Prim

var :: (?annotation :: a) => Name -> Expr a
var = A ?annotation . E.Var

lam :: (?annotation :: a) => Name -> Maybe (Type a Poly) -> Expr a -> Expr a
lam n t e = A ?annotation $ E.Lam n t e

tuple :: (?annotation :: a) => [Expr a] -> Expr a
tuple = A ?annotation . E.Tuple

casee :: (?annotation :: a) => Expr a -> [(Pat a, Expr a)] -> Expr a
casee e = A ?annotation . E.Case e

bind :: (?annotation :: a) => Name -> Pat a
bind = A ?annotation . E.Bind

match :: (?annotation :: a) => Name -> [Pat a] -> Pat a
match ps = A ?annotation . E.Match ps

tickvar :: (?annotation :: a) => Name -> Expr a
tickvar = A ?annotation . E.TickVar

tAbs :: (?annotation :: a) => Name -> Name -> Expr a -> Expr a
tAbs af k = A ?annotation . E.TickAbs af k

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
  P.PrimRec          -> pure . Prim $ PrimRec
  P.Tick             -> pure . Prim $ Tick
  P.Fix              -> pure . Prim $ Fix
  P.Fmap             -> pure . Prim $ Fmap
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
        
        (Prim Fmap, _) -> do
          pure $ GetFmap e2
        
        (GetFmap f, v) -> do
          fm <- lookupFmap ann v
          evalExprStep ((fm `app` f `app`) e2)
        
        {-
        primRec body x
        => body (fmap (\x -> (x, primRec body x)) x) 

        primRec body
        => \x -> body (fmap (\x -> (x, primRec body x)) x)
        -}
        (Prim PrimRec, _) -> do
          let oname = UName "__outer__"
          let ovar = var oname
          let iname = UName "__inner__"
          let ivar = var iname

          let conte = (prim P.PrimRec `app` e2) `app` ivar
          let etup = tuple [ivar, conte]
          let fmaplam = lam iname Nothing etup
          let fmape = (prim E.Fmap `app` fmaplam) `app` ovar
          let bdeapp = e2 `app` fmape 
          env <- getEnv
          let r = Closure env oname bdeapp
          pure $ r
        
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

{-
data NatF f = Z | S f.
Z : forall a. NatF a.
S : forall a. a -> NatF a.

instance Functor NatF where
  fmap f Z = Z
  fmap f (S n) = S (f n)
-}

data Ftor0 f = Ftor0 (forall a. (a, f))

instance Functor Ftor0 where
  fmap f (Ftor0 x) = Ftor0 (fst x, f (snd x))

data Ftor1 f = Ftor1 (forall a. a -> f) 
data Ftor2 f = Ftor2 (Int -> f)

instance Functor Ftor1 where
  fmap f (Ftor1 g) = Ftor1 (\x -> f (g x))

instance Functor Ftor2 where
  fmap f (Ftor2 g) = Ftor2 (\x -> f (g x))

data Ftor3 f = forall a. Ftor3 (a -> f) -- deriving (Functor)

instance Functor Ftor3 where
  fmap f (Ftor3 g) = Ftor3 (\x -> f (g x))

data Ftor4 f = Ftor4 f (Maybe f)

instance Functor Ftor4 where
  fmap f (Ftor4 x my) = Ftor4 (f x) (fmap f my)

data Ftor5 f = Ftor5 ((f -> Int) -> Int) deriving Functor


type TVarName = Name
deriveFunctor :: Datatype a -> Either String (Expr a)
deriveFunctor (E.Datatype {dtName, dtBound, dtConstrs}) =
  let vn = UName "#val"
      fn = UName "#f"
      tnm = fst . last $ dtBound -- TODO: make total
      A ann _ = head dtConstrs -- TODO: make total
  in  let ?annotation = ann
  in  lam fn Nothing . lam vn Nothing .
        casee (var vn) <$> traverse (deriveFunctorConstr (var fn) tnm) dtConstrs

deriveFunctorConstr :: forall a. Expr a -> TVarName -> E.Constr a -> Either String (Pat a, Expr a)
deriveFunctorConstr f tnm constr@(A ann (E.Constr nm args)) = do
  let (pat, assocs) = matchConstr constr
  let ?annotation = ann
  cargs <- traverse traversal assocs
  pure $ (pat, foldl folder (var nm) cargs)
  where
    folder acc darg = acc `app` darg

    traversal :: (?annotation :: a) => (Name, Type a Poly) -> Either String (Expr a)
    traversal (nm, ty) = do 
      fn <- deriveFmapArg f tnm ty
      pure $ fn `app` var nm

matchConstr :: E.Constr a -> (Pat a, [(Name, Type a Poly)])
matchConstr (A ann (E.Constr nm args)) = 
  let ?annotation = ann in
  let assocs = map (\(i, t) -> (MName i, t)) $ zip [0..] args
  in  (match nm $ map (bind . fst) assocs, assocs)

-- derive `fmap f` for functorial type variable `tnm` over type `typ`
-- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/DeriveFunctor
deriveFmapArg :: Expr a -> TVarName -> Type a Poly -> Either String (Expr a)
deriveFmapArg f tnm typ = go typ where
  go (A ann _) | not (E.inFreeVars tnm typ) = pure $ A ann $ E.Lam "x" Nothing $ (A ann $ E.Var "x")
  go (A ann typ') = 
    let ?annotation = ann in
    let id = lam "x" Nothing $ var "x"
    in case typ' of
      E.TFree _   -> pure id
      E.TExists _ -> pure id
      E.TVar nm | nm == tnm -> pure $ f
                | otherwise -> pure id
      E.Forall v k t -> go t -- TODO: !?!?!?
      E.Later t1 t2 -> 
        let af = UName "0af"
            k  = UName "0k"
        in  pure $ lam "x" Nothing $ tAbs af k (f `app` (var "x" `app` tickvar af))
      E.TTuple ts -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x" -- TODO: fmap for tuples
      t1 `E.TApp` t2 -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x"
      t1 E.:->: t2     -> do
        e1 <- cogo t1
        e2 <- go t2
        let x = UName "x"
            b = UName "b"
        pure $ lam x Nothing $ lam b Nothing $ e2 `app` (var x `app` (e1 `app` var b))

  cogo (A ann _) | not (E.inFreeVars tnm typ) = pure $ A ann $ E.Lam "x" Nothing $ (A ann $ E.Var "x")
  cogo (A ann typ') = 
    let ?annotation = ann in
    let id = lam "x" Nothing $ var "x"
    in case typ' of
      E.TFree _   -> pure id
      E.TExists _ -> pure id
      E.TVar nm | nm == tnm -> Left $ "type variable" ++ pps tnm ++ " is in a negative position"
                | otherwise -> pure id
      E.Forall v k t -> go t -- TODO: !?!?!?
      E.Later t1 t2 -> 
        let af = UName "0af"
            k  = UName "0k"
        in  pure $ lam "x" Nothing $ tAbs af k (f `app` (var "x" `app` tickvar af))
      E.TTuple ts -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x" -- TODO: fmap for tuples
      t1 `E.TApp` t2 -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x"
      t1 E.:->: t2     -> do
        e1 <- go t1
        e2 <- cogo t2
        let x = UName "x"
            b = UName "b"
        pure $ lam x Nothing $ lam b Nothing $ e2 `app` (var x `app` (e1 `app` var b))
  

        
        


-- deriveFunctor pname typ@(A ann typ') = 
--   case typ' of
--     TFree y     | y == forY  -> x
--                 | otherwise -> A a $ TFree y

--     TVar y      | y == forY  -> x
--                 | otherwise -> A a $ TVar y

--     TExists y   | y == forY  -> x
--                 | otherwise -> A a $ TExists y

--     Forall y k t  | y == forY -> A a $ Forall y k t 
--                   | otherwise -> A a $ Forall y k (subst x forY t)

--     Later  t1 t2  -> A a (Later (subst x forY t1) (subst x forY t2))


--     RecTy  t  -> A a $ RecTy (subst x forY t)
--     TTuple ts -> A a $ TTuple (map (subst x forY) ts)

--     t1 `TApp` t2 -> A a $ subst x forY t1 `TApp` subst x forY t2
    
--     t1 :->: t2 -> A a $ subst x forY t1 :->: subst x forY t2



evalProg :: Name -> Prog a -> Value a
evalProg mainnm pr =
  let er@(ElabRes {erDefs, erConstrs}) = collectDecls pr
      vconstrs = M.mapWithKey (\k v -> Right (Constr k [])) . unFreeCtx $ erConstrs
      initState = (M.map Left erDefs) `M.union` vconstrs
  in  case M.lookup mainnm erDefs of 
        Just maindef -> 
          runEvalM (updGlobals (const initState) >> evalExprCorec maindef) mempty
        Nothing -> Prim . RuntimeErr $ "No main definition of name " ++ pps mainnm ++ " found"

