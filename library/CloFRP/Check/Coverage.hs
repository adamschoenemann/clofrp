{-|
Module      : CloFRP.Check.Coverage
Description : Coverage checking of pattern matches

Based loosely on Conor McBride's StackOverflow answer at 
<https://stackoverflow.com/questions/7883023/algorithm-for-type-checking-ml-like-pattern-matching>
which in turn is based on Lennart Augustsson's "Compiling Pattern Matching".
My implementation however does not flag overlapping patterns but only fully
redundant patterns, which is what you'd want most of the time.
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CloFRP.Check.Coverage (coveredBy, unify, checkCoverage) where

import GHC.Exts (toList, IsList(..), coerce)
import Data.Maybe (catMaybes, isJust)
import Control.Monad (filterM, when, replicateM)
import Data.Foldable (foldlM)
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

-- | A 'Unifier' is just a list of mappings from names to patterns
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

-- | @unify pat1 pat2@ will return a unifier @u@ such that @refine u pat1 = pat2@
-- given that @pat1@ and @pat2@ are unifiable. If @pat1@ is more specific than
-- @pat2@, the empty unifier is returned.
-- >>> unify (Just x) (Just ())
-- Just [x ↦ ()]
-- 
-- >>> unify (Just ()) (Just x)
-- Just []
--
-- >>> unify (Just ()) (Cons x xs)
-- Nothing
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

-- | @refine uni pat@ will apply the substitutions in @uni@ to pat
-- >>> refine [x ↦ Nothing] (Just x)
-- Just Nothing
refine :: Unifier a -> Pat a -> Pat a
refine uni pat@(A ann pat') = refine' pat' where
  refine' (Bind nm)
    | Just replace <- lookup nm (coerce uni) = replace
    | otherwise = pat
  refine' (Match nm subpats) =
    A ann (Match nm (map (refine uni) subpats))
  refine' (PTuple subpats) =
    A ann (PTuple (map (refine uni) subpats))

-- | A unifier is either
-- * an injective renaming of variables or
-- * not an injective renaming of variables because of a specific mapping
data IsInjectiveResult a
  = Injective 
  | NotInjective Name

-- | @isInjective uni@ determines if @uni@ is and injective renaming
-- >>> isInjective [x ↦ y, z ↦ a]
-- Injective
-- >>> isInjective [x ↦ y, z ↦ Nil]
-- NotInjective z
isInjective :: Unifier a -> IsInjectiveResult a
isInjective (Unifier xs) = foldr folder Injective xs where
  folder (_, A _ (Bind _)) acc = acc
  folder (nm, A _ (Match _mnm _pats)) _acc = 
    NotInjective nm 
  folder (nm, A _ (PTuple _pats)) _acc = 
    NotInjective nm 

-- | A pattern matching clause that keeps track of the number of "usages".
-- in this context, a usage is when the clause is used to discharge
-- a constructor of a data-type
data Clause a = Clause { usages :: Int, pattern :: Pat a }
  deriving (Show, Eq)

instance Pretty (Clause a) where
  pretty (Clause uses pats) = "{" <+> pretty uses <> "," <+> pretty pats <+> "}"

newClause :: Pat a -> Clause a
newClause pat = Clause { usages = 0, pattern = pat }

useClause :: Clause a -> Clause a
useClause cl = cl { usages = usages cl + 1 }

-- | Check if a type is fully covered by a list of patterns
checkCoverage :: a -> PolyType a -> [Pat a] -> TypingM a ()
checkCoverage ann ty covering = do
  nm <- freshName
  withCtx (\c -> c <+ (nm .: ty)) $ coveredBy (A ann (Bind nm)) covering

-- | A \"stateful\" solution to coverage checking. We keep track of number of usages of each
-- clause. Every clause must be used at least once. Sequential tests should
-- make sure that redundant clauses are not reached and thus not used.
-- Here is a badly written example of
-- 
-- > case xs of
-- >   Nil -> ... 
-- >   Cons MkUnit (Cons y xs) -> ... 
-- >   Cons MkUnit xs -> ...
--
-- @
-- xs coveredBy [{0, Nil}, {0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}]
-- | split xs into [Nil, Cons `a `b]
-- \ Nil coveredBy [{0, Nil}, {0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}]
-- | \ Nil covers Nil so increase first covering to {1, Nil} 
-- \ Cons `a `b coveredBy [{1, Nil}, {0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}] 
--   \ Nil does not unify with Cons `a `b so try next
--   \ the unifier [`a ↦ MkUnit, `b ↦ Cons y xs] works, but not injective, so
--     we have to split on the first mapping
--     \ Cons MkUnit `b coveredBy [{0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}]
--       unifies with [`b ↦ (Cons y xs)] which is not injective so split on `b
--       \ Cons MkUnit Nil coveredBy [{0, Cons MkUnit (Cons y xs)}, {0, Cons MkUnit xs}]
--         \ first doesn't match, but second does with an injective renaming, so 
--           increase to {1, Cons MkUnit xs}
--       \ Cons MkUnit (Cons `c `d) coveredBy [{0, Cons MkUnit (Cons y xs)}, {1, Cons MkUnit xs}]
--         \ First unifies with the empty injective renaming, so increase to {1, Cons MkUnit (Cons y xs)}
-- @
-- 
-- Every clause is used once, so we're good!
coveredBy :: forall a. Pat a -> [Pat a] -> TypingM a ()
coveredBy idealPat coveringPats = do
  clauses <- check idealPat (map newClause coveringPats)
  let unreached = unusedPatterns clauses
  if length unreached > 0
    then unreachableCases unreached
    else pure ()
  where 
    unusedPatterns clauses = 
      let onlyUnused = \(Clause uses pat) -> if uses < 1 then Just pat else Nothing
      in  catMaybes (map onlyUnused clauses)

-- | Check that a pattern is covered by a list of clauses, returning the same
-- clauses but updated with their number of usages
check :: Pat a -> [Clause a] -> TypingM a [Clause a]
check ideal [] = rule "CoveredBy.Uncovered" (pretty ideal) >> uncoveredCases ideal
check ideal coverings@(cov : covs) = do
  rule "CoveredBy" (pretty (ideal, coverings)) 
  case unify ideal (pattern cov) of -- check if ideal unifies with cov
    -- if not, we move on to the next covering pattern without updating nothin'
    Nothing -> (cov :) <$> check ideal covs
    Just uni -> 
      case isInjective uni of
        -- if the unifier is injective we're done!
        Injective -> branch $ do 
          rule "CoveredBy.Injective" (pretty uni)
          -- return the clauses, we we'll update the current clause to mark its usage
          pure (useClause cov : covs)

        -- it is not injective because of 'binding'
        NotInjective binding -> branch $ do
          rule "CoveredBy.NotInjective" (pretty uni)
          patTy <- lookupTyTM binding -- get type of the binding
          constructors <- silentBranch $ getPatternsOfType patTy -- get constructors of type
          if null constructors 
            -- if the type has no constructors, then there is probably an error.
            -- we can't pattern match on types with no constructors at this point
            then error $ show $ "Cant match on a value of type" <+> pretty patTy
              <+> "because it has no constructors"
            -- else we make a new covering problem for each constructor of the type
            else branch $ do
              rule "CoveredBy.Split" (pretty binding <+> "into" <+> pretty constructors)
              splitProblems patTy binding coverings constructors
  where
    splitProblems patTy nm clauses cs =
      foldlM (\clauses' c -> splitProblem patTy nm clauses' c) clauses cs

    splitProblem patTy nm clauses constructor = do
      -- refine the ideal pattern, substituting 'constructor' for 'nm' in ideal
      let refined = refine [(nm, constructor)] ideal
      -- get a context with the subpatterns of constructor assigned to their
      -- appropriate type
      delta <- silentBranch $ checkPat constructor patTy
      -- check the refined pattern against clauses
      withCtx (const delta) $ branch $ check refined clauses

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



