{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloTT.Derive where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.List (genericLength)

import CloTT.Annotated
import CloTT.Pretty
import CloTT.AST.Expr
import CloTT.AST.Pat
import CloTT.AST.Type
import CloTT.AST.Name
import CloTT.AST.Datatype
import CloTT.AST.Helpers
import qualified CloTT.AST.Prim as P
import CloTT.Check.Contexts (ClassInstance(..))
import CloTT.Utils (safeLast, safeInit, (|->))

{-
data NatF f = Z | S f.
Z : forall a. NatF a.
S : forall a. a -> NatF a.

instance Functor NatF where
  fmap f Z = Z
  fmap f (S n) = S (f n)
-}

-- data Constraint = HasKind Kind

-- data InstanceResolver a
--   = NoConstraints Name -- NatF, Maybe
--   | Constraints [Constraint] Name

-- natFRes = NoConstraints "NatF"
-- maybeFRes = NoConstraints "Maybe"
-- listFRes = Constraint [HasKind Star] "ListF"

-- resolveInstance :: Type a 'Poly -> InstanceResolver -> TypingM a Bool
-- resolveInstance (A _ ty') ir =
--   case (ty', ir) of
--     (TFree n, NoConstraints n') -> n == n'
--     (TVar n,   -> S.singleton n
--     TExists n -> S.singleton n
--     TApp x y -> freeVars x `S.union` freeVars y
--     x :->: y  -> freeVars x `S.union` freeVars y
--     Forall n k t -> freeVars t `S.difference` S.singleton n
--     RecTy  t -> freeVars t 
--     TTuple ts -> S.unions $ map freeVars ts
--     Later t1 t2 -> freeVars t1 `S.union` freeVars t2



-- a giant hack of course
deriveClass :: Name -> Datatype a -> Either String (ClassInstance a)
deriveClass (UName "Functor") dt = deriveFunctor dt
deriveClass nm dt = Left $ show $ "Cannot derive" <+> pretty nm <+> "for" <+> (pretty $ dtName dt) <+> "since we can only derive functor atm."

deriveFunctor :: Datatype a -> Either String (ClassInstance a)
deriveFunctor (Datatype {dtName, dtBound = [], dtConstrs}) =
  Left $ show $ "Cannot derive functor for concrete type" <+> pretty dtName

deriveFunctor (Datatype {dtName, dtBound, dtConstrs = []}) =
  Left $ show $ "Cannot derive functor uninhabited  type" <+> pretty dtName

deriveFunctor (Datatype {dtName, dtBound = bs@(b:_), dtConstrs = cs@(A ann c1 : _)}) = do
  expr <- deriveFunctorDef ann (fst $ safeLast b bs) cs
  let ?annotation = ann
  let extrabs = map fst $ safeInit bs
  let nfa = foldl (tapp) (tfree dtName) (map tvar extrabs) -- nearlyFullyApplied
  let typ = forAll (extrabs ++ ["#a", "#b"]) $ (tvar "#a" `arr` tvar "#b") `arr` (nfa `tapp` tvar "#a") `arr` (nfa `tapp` tvar "#b")
  -- let fmapNm = UName $ show (pretty dtName <> "_fmap")
  let inst = ClassInstance { ciClassName = "Functor"
                           , ciInstanceTypeName = dtName
                           , ciParams = extrabs
                           , ciDictionary = M.singleton "fmap" (typ, expr)
                           }
  pure $ inst

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

    traversal :: (?annotation :: a) => (Name, Type a 'Poly) -> Either String (Expr a)
    traversal (nm', ty) = do 
      fn <- deriveFmapArg f tnm ty
      pure $ fn `app` var nm'

matchConstr :: Constr a -> (Pat a, [(Name, Type a 'Poly)])
matchConstr (A ann (Constr nm args)) = 
  let ?annotation = ann in
  let assocs = map (\(i, t) -> (UName ("#" ++ show i), t)) $ zip [(0::Int)..] args
  in  (match nm $ map (bind . fst) assocs, assocs)

-- derive `fmap f` for functorial type variable `tnm` over type `typ`
-- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/DeriveFunctor
deriveFmapArg :: Expr a -> TVarName -> Type a 'Poly -> Either String (Expr a)
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
      TTuple ts -> deriveFmapTuple f tnm ts -- pure $ lam "x" Nothing $ (A anno $ Fmap typ) `app` var "x" -- TODO: fmap for tuples
      t1 `TApp` t2 -> pure $ lam "x" Nothing $ (A anno $ Fmap typ) `app` var "x"
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
      TTuple ts -> pure $ lam "x" Nothing    $ (A anno $ Fmap typ) `app` var "x" -- TODO: fmap for tuples
      t1 `TApp` t2 -> pure $ lam "x" Nothing $ (A anno $ Fmap typ) `app` var "x"
      t1 :->: t2     -> do
        e1 <- go t1
        e2 <- cogo t2
        let x = UName "x"
            b = UName "b"
        pure $ lam x Nothing $ lam b Nothing $ e2 `app` (var x `app` (e1 `app` var b))
  
  ide = A anno $ Lam "x" Nothing (A anno $ Var "x")
  
deriveFmapTuple :: (?annotation :: a) => Expr a -> TVarName -> [Type a 'Poly] -> Either String (Expr a)
deriveFmapTuple f tnm ts = do
  let is = [0 .. genericLength ts - 1]
  let nms = map (UName . ("#" ++) . show) is
  fmaps <- traverse (deriveFmapArg f tnm) ts
  let es = zipWith (\f v -> f `app` v) fmaps (map var nms)
  pure $ lam' "x" $ casee (var "x") [ptuple (map bind nms) |-> tuple es]