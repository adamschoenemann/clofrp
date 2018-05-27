{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CloFRP.Check.Coverage (coveredBy, unify, checkCoverage) where

import GHC.Exts (toList, IsList(..), coerce)
import Data.Maybe (catMaybes, isJust)
import Control.Monad (filterM, when, replicateM)
import Debug.Trace (trace)
import Data.List (foldl')

import CloFRP.AST.Pat (Pat, Pat'(..))
import CloFRP.AST.Name (Name)
import CloFRP.Annotated (Annotated (..), (=%=))
import CloFRP.Check.TypingM ( TypingM(..), uncoveredCases, unreachableCases
                            , branch, freshName, nameNotFound, silentBranch, rule
                            , getDCtx, getCtx, withCtx
                            )
import CloFRP.Check.Contexts (lookupTy, (.:), (<+))
import CloFRP.Pretty
import CloFRP.AST.Type (PolyType, Type'(..))
import CloFRP.AST.Expr (Expr)
import CloFRP.Check.Destr (Destr)
import qualified CloFRP.Check.Destr as Destr
import CloFRP.Check.Utils (existentialize)
import CloFRP.Check.Subtyping (isSubtypeOf)
import CloFRP.Check.Pat (checkPat)

newtype Unifier a = Unifier [(Name, Pat a)]
  deriving (Show, Eq, Monoid)

instance IsList (Unifier a) where
  type Item (Unifier a) = (Name, Pat a)
  fromList xs = Unifier xs
  toList (Unifier m) = m

instance Pretty (Unifier a) where
  pretty (Unifier pairs) = 
    enclose "[" "]" $ cat $ punctuate "," 
      $ map (\(n,p) -> pretty n <+> "↦" <+> pretty p) pairs


unify :: Pat a -> Pat a -> Maybe (Unifier a)
unify (A _ pat1') p2@(A _ pat2') = unify' pat1' pat2' where
  unify' (Bind nm1) _ = Just [(nm1, p2)]
  unify' (Match _ _) (Bind _) = Just []
  unify' (Match nm1 subpats1) (Match nm2 subpats2)
    | nm1 == nm2 = 
      case () of
        _ | length subpats1 /= length subpats2 -> -- sanity check
            error "FATAL: Pattern with same name but different number of subpats"
          | null subpats1 ->
            Just []
          | otherwise -> 
            mconcat <$> (sequence $ (zipWith unify subpats1 subpats2))
    | otherwise =
      Nothing
  unify' (PTuple subpats1) (PTuple subpats2)
      | length subpats1 /= length subpats2 = -- sanity check
        error "FATAL: Tuple patterns with different number of subpats"
      | otherwise = 
        mconcat <$> (sequence $ (zipWith unify subpats1 subpats2))
  unify' _ _ = Nothing

refine :: Unifier a -> Pat a -> Pat a
refine uni pat@(A ann pat') = refine' pat' where
  refine' (Bind nm)
    | Just replace <- lookup nm (coerce uni) = replace
    | otherwise = pat
  refine' (Match nm subpats) =
    A ann (Match nm (map (refine uni) subpats))
  refine' (PTuple subpats) =
    A ann (PTuple (map (refine uni) subpats))

data IsInjectiveResult a
  = Injective 
  | NotInjective Name

isInjective :: Unifier a -> IsInjectiveResult a
isInjective (Unifier xs) = foldr folder Injective xs where
  folder (_, A _ (Bind _)) acc = acc
  folder (nm, A _ (Match _mnm _pats)) _acc = 
    NotInjective nm 
  folder (nm, A _ (PTuple _pats)) _acc = 
    NotInjective nm 
  folder _ acc  = acc

data Clause a = Clause { usages :: Int, pattern :: Pat a }
  deriving (Show, Eq)

instance Pretty (Clause a) where
  pretty (Clause uses pats) = "{" <+> pretty uses <> "," <+> pretty pats <+> "}"

newClause :: Pat a -> Clause a
newClause pat = Clause { usages = 0, pattern = pat }

useClause :: Clause a -> Clause a
useClause cl = cl { usages = usages cl + 1 }

checkCoverage :: a -> PolyType a -> [Pat a] -> TypingM a ()
checkCoverage ann ty covering = do
  nm <- freshName
  withCtx (\c -> c <+ (nm .: ty)) $ coveredBy (A ann (Bind nm)) covering

-- attempt at "stateful solution". keep track of number of usages of each
-- clause. Every clause must be used at least once. Sequential tests should
-- make sure that redundant clauses are not reached and thus not used
{-
  here is a badly written example
  xs coveredBy [{0, Nil}, {0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}]
  | split xs
  Nil coveredBy [{0, Nil}] <- increases to {1, Nil}
  Cons `a `b coveredBy [{0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}] 
  | split `a
  Cons MkUnit `b coveredBy [{0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}]
  | split `b
  Cons MkUnit Nil coveredBy [{0, Cons MkUnit xs}] <- increases to {1, Cons MkUnit xs}
  Cons MkUnit (Cons `c `d) coveredBy [{0, Cons MkUnit (Cons y xs)}, {1, Cons MkUnit xs}]
-}
coveredBy :: forall a. Pat a -> [Pat a] -> TypingM a ()
coveredBy idealPat coveringPats = do
  clauses <- check idealPat (map newClause coveringPats)
  let unreached = catMaybes $ map (\(Clause uses pat) -> if uses < 1 then Just pat else Nothing) clauses
  if length unreached > 0
    then unreachableCases unreached
    else pure ()
  where 
    check :: Pat a -> [Clause a] -> TypingM a [Clause a]
    check ideal [] = rule "CoveredBy.Uncovered" (pretty ideal) >> uncoveredCases ideal
    check ideal clauses@(cov : covs) = do
      rule "CoveredBy" (pretty (ideal, clauses)) 
      case unify ideal (pattern cov) of
        Nothing -> (cov :) <$> check ideal covs
        Just uni -> 
          case isInjective uni of
            Injective -> branch $ do
              rule "CoveredBy.Injective" (pretty uni)
              pure (useClause cov : covs)

            NotInjective binding -> branch $ do
              rule "CoveredBy.NotInjective" (pretty uni)
              patTy <- lookupTyTM binding
              constructors <- reverse <$> (silentBranch $ getPatternsOfType patTy)
              if null constructors
                then error $ show $ "Cant match on a value of type" <+> pretty patTy
                  <+> "because it has no constructors"
                else branch $ do
                  rule "CoveredBy.Split" (pretty binding <+> "into" <+> pretty constructors)
                  splitProblems ideal patTy binding clauses constructors

    splitProblems ideal _patTy _nm clauses [] = pure clauses
    splitProblems ideal patTy nm clauses (c:cs) = do
        clauses' <- splitProblem ideal patTy nm clauses c
        splitProblems ideal patTy nm clauses' cs

    splitProblem ideal patTy nm clauses constructor = do
      let refined = refine [(nm, constructor)] ideal
      delta <- silentBranch $ checkPat constructor patTy
      withCtx (const delta) $ branch $ check refined clauses


-- | deprecated
retainInvariant :: Foldable t => Pat a -> t (Pat a) -> [Pat a]
retainInvariant uniWith toUni =
  reverse $ foldl' folder [] toUni where
    folder acc p = 
      case normalizePattern uniWith p of
        Nothing -> acc
        Just p'
          | (null acc) -> trace "acc is not null" $ p' : acc
          | p' =%= p -> trace "not refinement happened" $ p' : acc
          | otherwise -> acc

-- | Normalizes the second pattern to the first patterns form if they match
-- | deprecated
normalizePattern :: Pat a -> Pat a -> Maybe (Pat a)
normalizePattern pat1@(A _ pat1') pat2@(A ann pat2') = go pat1' pat2' where
  go (Bind _) _ = pure pat2
  go (Match nm1 subps1) (Match nm2 subps2) 
    | nm1 == nm2 && length subps1 == length subps2 =
      A ann . Match nm2 <$> sequence (zipWith normalizePattern subps1 subps2)
    | otherwise = Nothing
  go (Match _ _) (Bind _) = pure pat1


lookupTyTM :: Name -> TypingM a (PolyType a)
lookupTyTM nm = do
  mty <- lookupTy nm <$> getCtx
  case mty of 
    Nothing -> nameNotFound nm
    Just ty -> pure ty

getPatternsOfType :: PolyType a -> TypingM a [Pat a]
getPatternsOfType qtype@(A ann qtype') = do
  rule "GetPatternsOfType" (pretty qtype)
  case qtype' of 
    TTuple ts -> 
      (: []) . A ann . PTuple <$> replicateM (length ts) (A ann . Bind <$> freshName)
    _ -> do
      destrs <- branch $ getDestrsOfType qtype
      traverse (destrToPat ann) destrs

destrToPat :: a -> Destr a -> TypingM a (Pat a)
destrToPat ann destr = do
  let name = Destr.name destr
  let args = Destr.args destr
  subvars <- traverse (\_ -> A ann . Bind <$> freshName) args
  pure (A ann (Match name subvars))


getDestrsOfType :: PolyType a -> TypingM a [Destr a]
getDestrsOfType qtype@(A ann _) = do
  destrCtx <- getDCtx
  let destrs = map snd $ toList destrCtx
  filterM onlySubtypes destrs
  where
    onlySubtypes destr = do
      (delta, edestr) <- existentialize ann destr
      withCtx (const delta) $ Destr.typ edestr `isSubtypeOf` qtype



