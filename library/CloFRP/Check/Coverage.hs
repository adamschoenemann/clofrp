{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CloFRP.Check.Coverage (coveredBy, unify) where

import GHC.Exts (toList, IsList(..), coerce)
import Data.Maybe (isJust)
import Data.Foldable (foldrM)
import Control.Monad (filterM)
import Debug.Trace (trace)

import CloFRP.AST.Pat (Pat, Pat'(..))
import CloFRP.AST.Name (Name)
import CloFRP.Annotated (Annotated (..))
import CloFRP.Check.TypingM ( TypingM(..), uncoveredPattern, unreachablePattern
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
import CloFRP.Check.Pat (checkDestr, checkPat)

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
  unify'(Bind nm1) _ = Just (Unifier [(nm1, p2)])
  unify' (Match nm1 subpats1) (Match nm2 subpats2)
    | nm1 == nm2 = 
      case () of
        _ | length subpats1 /= length subpats2 -> -- sanity check
            error "FATAL: Pattern with same name but different number of subpats"
          | null subpats1 ->
            Just (Unifier [])
          | otherwise -> 
            mconcat <$> (sequence $ (zipWith unify subpats1 subpats2))
    | otherwise =
      Nothing
  unify' _ _ = Nothing
  
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


coveredBy :: Pat a -> [Pat a] -> TypingM a ()
coveredBy ideal [] = rule "CoveredBy.Uncovered" (pretty ideal) >> uncoveredPattern ideal
coveredBy ideal pats@(covering : coverings) = do
  rule "CoveredBy" (pretty (ideal, pats)) 
  let uniM = unify ideal covering
  case uniM of 
    Nothing -> 
      error "FATAL: coveredBy must be called with unifying patterns"

    Just uni ->
      case isInjective uni of
        Injective -> do
          branch $ rule "CoveredBy.Injective" (pretty uni)
          case () of
            _ | null coverings -> 
                branch $ rule "CoveredBy.Discharge" (pretty (ideal, pats))
                          >> pure ()
              | otherwise -> unreachablePattern ideal

        NotInjective binding (_constructor, _pats) -> do
          branch $ rule "CoveredBy.NotInjective" (pretty uni)
          patTy <- lookupTyTM binding
          constructors <- reverse <$> (silentBranch $ getPatternsOfType patTy)
          branch $ do
            rule "CoveredBy.Split" (pretty constructors)
            traverse (splitProblem patTy binding) constructors >> pure ()
  where
    splitProblem patTy nm constructor = do
      let refined = refine [(nm, constructor)] ideal
      delta <- silentBranch $ checkPat constructor patTy
      withCtx (const delta) $ branch $ coveredBy refined (onlyUnifying refined)
    
    onlyUnifying uniWith =
      let result = filter (isJust . unify uniWith) pats
        -- const (show $ "unify with" <+> pretty uniWith <+> pretty pats <+> "-->" <+> pretty result) $ 
      in  result

lookupTyTM :: Name -> TypingM a (PolyType a)
lookupTyTM nm = do
  mty <- lookupTy nm <$> getCtx
  case mty of 
    Nothing -> nameNotFound nm
    Just ty -> pure ty

freshPatternsFromName :: Name -> TypingM a [Pat a]
freshPatternsFromName nm = do 
  ty <- lookupTyTM nm
  silentBranch $ getPatternsOfType ty

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



