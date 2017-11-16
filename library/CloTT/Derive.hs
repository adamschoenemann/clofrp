{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloTT.Derive where

import CloTT.Annotated
import CloTT.Pretty
import CloTT.AST.Expr
import CloTT.AST.Pat
import CloTT.AST.Type
import CloTT.AST.Name
import CloTT.AST.Datatype
import CloTT.AST.Helpers
import qualified CloTT.AST.Prim as P

{-
data NatF f = Z | S f.
Z : forall a. NatF a.
S : forall a. a -> NatF a.

instance Functor NatF where
  fmap f Z = Z
  fmap f (S n) = S (f n)
-}

-- total definition of last
lst :: a -> [a] -> a
lst d [] = d
lst d [x] = x
lst d (x:xs) = lst d xs

-- total def of init
inits :: [a] -> [a]
inits [] = []
inits [x] = []
inits (x:xs) = x : inits xs

-- a giant hack of course
deriveClass :: Name -> Datatype a -> Either String (Name, Type a Poly, Expr a)
deriveClass (UName "Functor") dt = deriveFunctor dt
deriveClass nm dt = Left $ show $ "Cannot derive" <+> pretty nm <+> "for" <+> (pretty $ dtName dt) <+> "since we can only derive functor atm."

deriveFunctor :: Datatype a -> Either String (Name, Type a Poly, Expr a)
deriveFunctor (Datatype {dtName, dtBound = [], dtConstrs}) = Left $ show $ "Cannot derive functor for concrete type" <+> pretty dtName
deriveFunctor (Datatype {dtName, dtBound, dtConstrs = []}) = Left $ show $ "Cannot derive functor uninhabited  type" <+> pretty dtName
deriveFunctor (Datatype {dtName, dtBound = bs@(b:_), dtConstrs = cs@(A ann c1 : _)}) = do
  expr <- deriveFunctorDef ann (fst $ lst b bs) cs
  let ?annotation = ann
  let extrabs = map fst $ inits bs
  let nfa = foldl (tapp) (tfree dtName) (map tvar extrabs) -- nearlyFullyApplied
  let typ = forAll (extrabs ++ ["#a", "#b"]) $ (tvar "#a" `arr` tvar "#b") `arr` (nfa `tapp` tvar "#a") `arr` (nfa `tapp` tvar "#b")
  let fmapNm = UName $ show (pretty dtName <> "_fmap")
  pure (fmapNm, typ, expr)

type TVarName = Name

deriveFunctorDef :: a -> Name -> [Constr a] -> Either String (Expr a)
deriveFunctorDef ann tnm cs =
  let vn = UName "#val"
      fn = UName "#f"
  in  let ?annotation = ann
  in  lam fn Nothing . lam vn Nothing .
        casee (var vn) <$> traverse (deriveFunctorConstr (var fn) tnm) cs

deriveFunctorConstr :: forall a. Expr a -> TVarName -> Constr a -> Either String (Pat a, Expr a)
deriveFunctorConstr f tnm constr@(A ann (Constr nm args)) = do
  let (pat, assocs) = matchConstr constr
  let ?annotation = ann
  cargs <- traverse traversal assocs
  pure $ (pat, foldl folder (var nm) cargs)
  where
    folder acc darg = acc `app` darg

    traversal :: (?annotation :: a) => (Name, Type a Poly) -> Either String (Expr a)
    traversal (nm', ty) = do 
      fn <- deriveFmapArg f tnm ty
      pure $ fn `app` var nm'

matchConstr :: Constr a -> (Pat a, [(Name, Type a Poly)])
matchConstr (A ann (Constr nm args)) = 
  let ?annotation = ann in
  let assocs = map (\(i, t) -> (UName ("#" ++ show i), t)) $ zip [(0::Int)..] args
  in  (match nm $ map (bind . fst) assocs, assocs)

-- derive `fmap f` for functorial type variable `tnm` over type `typ`
-- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/DeriveFunctor
deriveFmapArg :: Expr a -> TVarName -> Type a Poly -> Either String (Expr a)
deriveFmapArg f tnm typ@(A anno _) = go typ where
  go (A ann _) | not (inFreeVars tnm typ) = pure $ A ann $ Lam "x" Nothing $ (A ann $ Var "x")
  go (A ann typ') = 
    let ?annotation = ann 
    in  case typ' of
      TFree _   -> pure ide
      TExists _ -> pure ide
      TVar nm | nm == tnm -> pure $ f
                | otherwise -> pure ide
      Forall v k t -> go t -- TODO: !?!?!?
      Later t1 t2 -> 
        let af = UName "0af"
            k  = UName "0k"
        in  pure $ lam "x" Nothing $ tAbs af k (f `app` (var "x" `app` tickvar af))
      TTuple ts -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x" -- TODO: fmap for tuples
      t1 `TApp` t2 -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x"
      t1 :->: t2     -> do
        e1 <- cogo t1
        e2 <- go t2
        let x = UName "x"
            b = UName "b"
        pure $ lam x Nothing $ lam b Nothing $ e2 `app` (var x `app` (e1 `app` var b))

  cogo (A ann _) | not (inFreeVars tnm typ) = pure $ A ann $ Lam "x" Nothing $ (A ann $ Var "x")
  cogo (A ann typ') = 
    let ?annotation = ann 
    in  case typ' of
      TFree _   -> pure ide
      TExists _ -> pure ide
      TVar nm | nm == tnm -> Left $ "type variable " ++ pps tnm ++ " is in a negative position"
                | otherwise -> pure ide
      Forall v k t -> go t -- TODO: !?!?!?
      Later t1 t2 -> 
        let af = UName "0af"
            k  = UName "0k"
        in  pure $ lam "x" Nothing $ tAbs af k (f `app` (var "x" `app` tickvar af))
      TTuple ts -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x" -- TODO: fmap for tuples
      t1 `TApp` t2 -> pure $ lam "x" Nothing $ prim P.Fmap `app` var "x"
      t1 :->: t2     -> do
        e1 <- go t1
        e2 <- cogo t2
        let x = UName "x"
            b = UName "b"
        pure $ lam x Nothing $ lam b Nothing $ e2 `app` (var x `app` (e1 `app` var b))
  
  ide = A anno $ Lam "x" Nothing (A anno $ Var "x")
  

        
        


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