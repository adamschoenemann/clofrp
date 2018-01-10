
module CloFRP.Check.Unify where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import CloFRP.AST.Name
import CloFRP.AST.Type
import CloFRP.Annotated
import CloFRP.Pretty

type Subst a = Map Name (PolyType a)

type UnifyM a = Either String a

throwError :: String -> UnifyM a
throwError = Left

nullSubst :: Subst a
nullSubst = mempty

applySubst :: Subst a -> PolyType a -> PolyType a
applySubst m1 ty = M.foldrWithKey (\nm x acc -> subst x nm acc) ty m1

compose :: Subst a -> Subst a -> Subst a
compose m1 m2 = M.map (applySubst m1) m2 `M.union` m2

bind :: Name -> PolyType a -> UnifyM (Subst a)
bind nm pt
  | nm `inFreeVars` pt = throwError (show nm ++ " occurs in " ++ pps pt)
  | otherwise          = pure (M.singleton nm pt)

cannotUnify :: Name -> Name -> UnifyM a
cannotUnify x y = throwError ("Cannot unify " ++ show x ++ " with " ++ show y)

kindMismatch :: (Name, Kind) -> (Name, Kind) -> UnifyM a
kindMismatch x y = throwError ("Cannot unify " ++ show x ++ " with " ++ show y)

unificationMismatch :: [PolyType a] -> [PolyType a] -> UnifyM a
unificationMismatch ts1 ts2 = throwError ("Unification mismatch: " ++ pps ts1 ++ " versus " ++ pps ts2)

unifier :: PolyType a -> PolyType a -> UnifyM (Subst a)
unifier type1 type2
  | type1 =%= type2 = pure nullSubst
  | otherwise = go type1 type2
  where 
    go ty1@(A _ ty1') ty2@(A _ ty2') = case (ty1', ty2') of
      (TExists x, _) -> bind x ty2
      (_, TExists x) -> bind x ty1
      (TFree x, TFree y) -> if x == y then nullSubst else cannotUnify x y
      (TVar  x, TFree y) -> if x == y then nullSubst else cannotUnify x y
      (l1 `TApp` r1, l2 `TApp` r2) -> unifyMany [l1, r1] [l2, r2]
      (l1 :->: r1, l2 :->: r2) -> unifyMany [l1, r2] [l2, r2]
      (Forall n1 k1 t1, Forall n2 k2 t2) 
        | k1 /= k2 -> kindMistmatch (n1,k1) (n2,k2)
        |

      RecTy  t -> A a . RecTy <$> asMonotype t

      TTuple ts -> A a . TTuple <$> sequence (map asMonotype ts)
      Later t1 t2 -> (\x y -> A a $ Later x y) <$> asMonotype t1 <*> asMonotype t2

unifyMany :: [PolyType a] -> [PolyType a] -> UnifyM (Subst a)
unifyMany [] [] = return nullSubst
unifyMany (t1 : ts1) (t2 : ts2) = do
  s1 <- unifier t1 t2
  s2 <- unifyMany (map (applySubsts s1) ts1) (map (applySubsts s1) ts2)
  pure (s1 `compose` s2)
unifyMany t1 t2 = do
  unificationMismatch t2 t2
