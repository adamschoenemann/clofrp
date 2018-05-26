{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CloFRP.Check.Coverage ( coveredBy, unifyStrict, unifyNonStrict
                             , normalizePattern, retainInvariant
                             ) where

import GHC.Exts (toList, IsList(..), coerce)
import Data.Maybe (catMaybes, isJust)
import Control.Monad (filterM, when)
import Debug.Trace (trace)
import Data.List (foldl')

import CloFRP.AST.Pat (Pat, Pat'(..))
import CloFRP.AST.Name (Name)
import CloFRP.Annotated (Annotated (..), (=%=))
import CloFRP.Check.TypingM ( TypingM(..), uncoveredCases, unreachableCases
                            , branch, freshName, nameNotFound, silentBranch, rule
                            , getDCtx, getCtx, withCtx
                            )
import CloFRP.Check.Contexts (lookupTy)
import CloFRP.Pretty
import CloFRP.AST.Type (PolyType)
import CloFRP.Check.Destr (Destr)
import qualified CloFRP.Check.Destr as Destr
import CloFRP.Check.Utils (existentialize)
import CloFRP.Check.Subtyping (isSubtypeOf)
import CloFRP.Check.Pat (checkPat)

data Strategy = Strict | NonStrict

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


unify :: Strategy -> Pat a -> Pat a -> Maybe (Unifier a)
unify ut (A _ pat1') p2@(A _ pat2') = unify' pat1' pat2' where
  unify' (Bind nm1) _ = Just [(nm1, p2)]
  unify' (Match _ _) (Bind _) = 
    case ut of 
      Strict -> Nothing
      NonStrict -> Just []
  unify' (Match nm1 subpats1) (Match nm2 subpats2)
    | nm1 == nm2 = 
      case () of
        _ | length subpats1 /= length subpats2 -> -- sanity check
            error "FATAL: Pattern with same name but different number of subpats"
          | null subpats1 ->
            Just []
          | otherwise -> 
            mconcat <$> (sequence $ (zipWith (unify ut) subpats1 subpats2))
    | otherwise =
      Nothing
  unify' _ _ = Nothing

unifyStrict, unifyNonStrict :: Pat a -> Pat a -> Maybe (Unifier a)
unifyStrict    = unify Strict
unifyNonStrict = unify NonStrict
  
refine :: Unifier a -> Pat a -> Pat a
refine uni pat@(A ann pat') = refine' pat' where
  refine' (Bind nm)
    | Just replace <- lookup nm (coerce uni) = replace
    | otherwise = pat
  refine' (Match nm subpats) =
    A ann (Match nm (map (refine uni) subpats))

data IsInjectiveResult a
  = Injective 
  | NotInjective Name (Name, [Pat a])

isInjective :: Unifier a -> IsInjectiveResult a
isInjective (Unifier xs) = foldr folder Injective xs where
  folder (_, A _ (Bind _)) acc = acc
  folder (nm, A _ (Match mnm pats)) _acc = 
    NotInjective nm (mnm, pats)
  folder _ acc@(NotInjective _ _)  = acc



data Clause a = Clause { usages :: Int, pattern :: Pat a }

newClause :: Pat a -> Clause a
newClause pat = Clause { usages = 0, pattern = pat }

useClause :: Clause a -> Clause a
useClause cl = cl { usages = usages cl + 1 }

-- attempt at "stateful solution". keep track of number of usages of each
-- clause. Every clause must be used at least once. Sequential tests should
-- make sure that redundant clauses are not reached and thus not used
checkCoverage :: Pat a -> [Pat a] -> TypingM a ()
checkCoverage idealPat coveringPats = 
  check idealPat (map newClause coveringPats)
  where 
    check ideal [] = rule "CoveredBy.Uncovered" (pretty ideal) >> uncoveredCases ideal
    check ideal (cov : covs) =
      case unify NonStrict ideal (pattern cov) of
        Nothing -> cov . (:) <$> check ideal covs
        Just uni -> 
          case isInjective uni of
            Injective -> branch $ do
              rule "CoveredBy.Injective" (pretty uni)
              pure (useClause cov : covs)


            NotInjective binding (_constructor, _pats) -> branch $ do
              rule "CoveredBy.NotInjective" (pretty uni)
              patTy <- lookupTyTM binding
              constructors <- reverse <$> (silentBranch $ getPatternsOfType patTy)
              branch $ do
                rule "CoveredBy.Split" (pretty binding <+> "into" <+> pretty constructors)
                splitProblems patTy binding constructors




coveredBy :: Pat a -> [Pat a] -> TypingM a ()
coveredBy ideal [] = rule "CoveredBy.Uncovered" (pretty ideal) >> uncoveredCases ideal
coveredBy ideal pats@(covering : coverings) = do
  rule "CoveredBy" (pretty (ideal, pats)) 
  let uniM = unifyNonStrict ideal covering
  case uniM of 
    Nothing -> 
      error "FATAL: coveredBy must be called with unifying patterns"

    Just uni ->
      case isInjective uni of
        Injective -> branch $ do
          rule "CoveredBy.Injective" (pretty uni)
          case coverings of
            [] -> branch $ do 
              rule "CoveredBy.Discharge" (pretty (ideal, pats))
              pure ()
            xs@(_:_) -> branch $ do
              rule "CoveredBy.Unreachable" (pretty (ideal, pats))
              unreachableCases xs

        NotInjective binding (_constructor, _pats) -> branch $ do
          rule "CoveredBy.NotInjective" (pretty uni)
          patTy <- lookupTyTM binding
          constructors <- reverse <$> (silentBranch $ getPatternsOfType patTy)
          branch $ do
            rule "CoveredBy.Split" (pretty binding <+> "into" <+> pretty constructors)
            splitProblems patTy binding constructors
  where
    splitProblems _patTy _nm [] = pure ()
    splitProblems patTy nm (c:cs) = 
        splitProblem (null cs) patTy nm c
          >> splitProblems patTy nm cs

    splitProblem isLast patTy nm constructor = do
      let refined = refine [(nm, constructor)] ideal
      delta <- silentBranch $ checkPat constructor patTy
      let retain = 
            if isLast
              then \ref -> catMaybes . map (normalizePattern ref) -- be strict about
              else retainInvariant -- be loose about it
      when isLast $ rule "IsLast" ""
      withCtx (const delta) $ branch $ coveredBy refined (retain refined pats)
    
      -- let result = filter (isJust . normalizePattern uniWith) toUni
      -- in  trace (show $ "unify with" <+> pretty uniWith <+> pretty pats <+> "-->" <+> pretty result) $ result
      -- in  result

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

-- freshPatternsFromName :: Name -> TypingM a [Pat a]
-- freshPatternsFromName nm = do 
--   ty <- lookupTyTM nm
--   silentBranch $ getPatternsOfType ty

getPatternsOfType :: PolyType a -> TypingM a [Pat a]
getPatternsOfType qtype@(A ann _) = do
  rule "GetPatternsOfType" (pretty qtype)
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



