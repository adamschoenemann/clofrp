{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloFRP.Derive where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.List (genericLength, foldl')

import CloFRP.Annotated
import CloFRP.Pretty
import CloFRP.AST.Expr
import CloFRP.AST.Pat
import CloFRP.AST.Type
import CloFRP.AST.Kind
import CloFRP.AST.Name
import CloFRP.AST.Datatype
import CloFRP.AST.Helpers
import qualified CloFRP.AST.Prim as P
import CloFRP.Check.Contexts (ClassInstance(..))
import CloFRP.Utils (safeLast, safeInit, (|->))

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
deriveClass nm dt =
  Left $ show $ "Cannot derive" <+> pretty nm <+> "for" 
      <+> (pretty $ dtName dt) <+> "since we can only derive functor atm."

-- | Derive functor for a data-type (or fail if impossible)
deriveFunctor :: Datatype a -> Either String (ClassInstance a)
deriveFunctor (Datatype {dtName, dtBound = []}) =
  Left $ show $ "Cannot derive functor for concrete type" <+> pretty dtName
deriveFunctor (Datatype {dtName, dtConstrs = []}) =
  Left $ show $ "Cannot derive functor uninhabited  type" <+> pretty dtName
deriveFunctor (Datatype {dtName, dtBound = bs@(b:_), dtConstrs = cs@(A ann _ : _)}) = do
  let (bnm, bk) = safeLast b bs                           -- the last bound variable in bs, or b if bs = []
  checkKind (bnm, bk)                                     -- check that the kind of bnm is correct (*)
  expr <- deriveFmapDef ann bnm cs                        -- derive the definition of the functor
  let ?annotation = ann                                   -- use ann for implicit anotations
  let extrabs = map fst $ safeInit bs                     -- take all type-variables except the last (which we're functorial over)
  let nfa = foldl' tapp (tfree dtName) (map tvar extrabs) -- The nearly fully applied type
  -- the type for fmap
  let typ = forAllK (safeInit bs ++ [(bnm, Star), ("#b", Star)]) $ 
              (tvar bnm `arr` tvar "#b") `arr` (nfa `tapp` tvar bnm) `arr` (nfa `tapp` tvar "#b")
  -- create the class instance
  let inst = ClassInstance { ciClassName        = "Functor"
                           , ciInstanceTypeName = dtName
                           , ciParams           = extrabs
                           , ciDictionary       = M.singleton "fmap" (typ, expr)
                           }
  pure $ inst
  where
    checkKind (_, Star) = pure ()
    checkKind (nm,k)   = Left $ pps nm ++ " must have kind * but had kind " ++ pps k

type TVarName = Name

-- | Derive the definition of fmap
deriveFmapDef :: a -> Name -> [Constr a] -> Either String (Expr a)
deriveFmapDef ann tnm cs =
  let vn = UName "val"
      fn = UName "f"
  in  let ?annotation = ann
  in  lam' fn . lam' vn .
        casee (var vn) <$> traverse (deriveFmapConstr (var fn) tnm) cs

-- | Derive a clause of fmap for a constructor
deriveFmapConstr :: forall a. Expr a -> TVarName -> Constr a -> Either String (Pat a, Expr a)
deriveFmapConstr f tnm constr@(A ann (Constr nm _args)) = do
  let (pat, assocs) = matchConstr constr
  let ?annotation = ann
  cargs <- traverse traversal assocs
  pure $ (pat, foldl' folder (var nm) cargs)
  where
    folder acc darg = acc `app` darg

    traversal :: (?annotation :: a) => (Name, Type a 'Poly) -> Either String (Expr a)
    traversal (nm', ty) = do 
      fn <- deriveFmapArg f tnm ty
      pure $ fn `app` var nm'

matchConstr :: Constr a -> (Pat a, [(Name, Type a 'Poly)])
matchConstr (A ann (Constr nm args)) = 
  let ?annotation = ann in
  let assocs = map (\(i, t) -> (UName ("x" ++ show i), t)) $ zip [(0::Int)..] args
  in  (match nm $ map (bind . fst) assocs, assocs)

-- | Derive `fmap f` for functorial type variable `tnm` over type `typ`
-- https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/DeriveFunctor
deriveFmapArg :: Expr a -> TVarName -> Type a 'Poly -> Either String (Expr a)
deriveFmapArg f tnm typ@(A anno _) = go typ where
  go typ2 | not (inFreeVars tnm typ2) = pure ide
  go (A ann typ') =
    let ?annotation = ann 
    in  case typ' of
      TFree _   -> pure ide
      TExists _ -> Left "existentials are not part of the concrete syntax"
      TVar nm | nm == tnm -> pure $ f
              | otherwise -> pure ide
      Forall v k t -> go t
      Later t1 t2 -> do
        let af = UName "af"
        k <- extractKappa t1
        e2 <- go t2
        pure $ lam' "x" $ tAbs af k (e2 `app` (var "x" `app` tickvar af))
      TTuple ts -> deriveFmapTuple f tnm ts 
      t1 `TApp` t2 -> pure $ lam' "x" $ (A anno $ Fmap t1) `app` f `app` var "x"
      t1 :->: t2     -> do
        e1 <- cogo t1
        e2 <- go t2
        let x = UName "x"
            b = UName "b"
        pure $ lam' x $ lam' b $ e2 `app` (var x `app` (e1 `app` var b))
      RecTy t -> Left $ "Cannot derive functor for recursive types"
        -- let x1 = UName "x1"
        --     x2 = UName "x2"
        --     x3 = UName "x3"
        -- fmapinner <- deriveFmapArg f tnm t
        -- pure $ letE (bind "snd") snde $ lam' x1 $ primRec t `app` (lam' x2 $ foldE `app` (fmapinner `app` (lam' x3 $ f `app` (var "snd" `app` var x3)) `app` var x2)) `app` var x1

  cogo typ2 | not (inFreeVars tnm typ2) = pure ide
  cogo (A ann typ') = 
    let ?annotation = ann 
    in  case typ' of
      TFree _   -> pure ide
      TExists _ -> Left "existentials are not part of the concrete syntax"
      TVar nm | nm == tnm -> Left $ "type variable " ++ pps tnm ++ " is in a negative position"
              | otherwise -> pure ide
      Forall v k t -> go t 
      Later t1 t2 -> do
        let af = UName "af"
        k <- extractKappa t1
        e2 <- go t2
        pure $ lam' "x" $ tAbs af k (e2 `app` (var "x" `app` tickvar af))
      TTuple ts    -> deriveFmapTuple f tnm ts
      t1 `TApp` t2 -> pure $ lam' "x" $ (A anno $ Fmap t1) `app` f `app` var "x"
      t1 :->: t2     -> do
        e1 <- go t1
        e2 <- cogo t2
        let x = UName "x"
            b = UName "b"
        pure $ lam' x $ lam' b $ e2 `app` (var x `app` (e1 `app` var b))
      RecTy t -> Left $ "Cannot derive functor for recursive types"
  
  ide = A anno $ Lam "x" Nothing (A anno $ Var "x")
  -- snde :: (?annotation :: a) => Expr a
  -- snde = A ?annotation $ Ann (lam' "tup" $ casee (var "tup") [ptuple [bind "_", bind "x_2"] |-> var "x_2"]) sndty where
  --   sndty = forAll ["a","b"] $ ttuple [tvar "a", tvar "b"] `arr` tvar "b"

deriveFmapTuple :: (?annotation :: a) => Expr a -> TVarName -> [Type a 'Poly] -> Either String (Expr a)
deriveFmapTuple f tnm ts = do
  let is = [(0::Int) .. genericLength ts - 1]
  let nms = map (UName . ("x" ++) . show) is
  fmaps <- traverse (deriveFmapArg f tnm) ts
  let es = zipWith (\f v -> f `app` v) fmaps (map var nms)
  pure $ lam' "x" $ casee (var "x") [ptuple (map bind nms) |-> tuple es]