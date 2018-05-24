{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloFRP.Check.Pat where

import Data.Foldable (foldlM)
import Data.List (genericLength)

import CloFRP.Check.TypingM 
import CloFRP.Check.Destr (Destr(..))
import CloFRP.Check.Contexts ( LocalCtx(..), CtxElem(..), (<+), isInContext
                             , Context(..), ctxFind, findAssigned, insertAt'
                             , splitCtx', before', Binding(..)
                             )
import CloFRP.AST.Type (Type'(..), PolyType)
import CloFRP.AST.Kind (Kind(..))
import CloFRP.AST.Name (Name(..))
import CloFRP.AST.Pat (Pat, Pat'(..))
import CloFRP.Annotated (Annotated(..))
import CloFRP.Pretty
import CloFRP.Check.Utils (existentialize)
import CloFRP.Check.Subtyping (subtypeOf)

checkPat :: Pat a -> PolyType a -> TypingM a (LocalCtx a)
checkPat pat@(A ann p) ty = do
  ctx <- getCtx
  dctx <- getDCtx
  rule "CheckPat" (pretty pat <+> "<=" <+> pretty ty)
  case p of
    Bind nm -> pure $ ctx <+ (LetB, nm) `HasType` ty

    Match nm pats -> case query nm dctx of
      Nothing    -> otherErr $ "Pattern " ++ show nm ++ " not found in context."
      Just destr -> branch $ checkDestr destr pats ty

    PTuple pats -> 
      -- generate a tuple destructor of length (length pats)
      let plen = genericLength pats
          dname = UName $ "tuple_" ++ show plen
          dbound = map (\x -> (DeBruijn x, Star)) [0 .. (plen - 1)]
          dargs = map (A ann . TVar . fst) dbound
          dtyp = A ann $ TTuple $ dargs
          d = Destr {name = dname, bound = dbound, typ = dtyp, args = dargs}
      in  branch $ checkDestr d pats ty

-- | In a context, check a destructor against a list of patterns and an expected type.
-- if it succeeds, it binds the names listed in the pattern match to the input context
checkDestr :: Destr a -> [Pat a] -> PolyType a -> TypingM a (LocalCtx a)
checkDestr d@(Destr {name, args}) pats expected@(A ann _)
  | length pats /= length args =
      otherErr $ show $ "Expected" <+> pretty (length args)
             <+> "arguments to" <> pretty name <+> "but got" <+> pretty (length pats)
  | otherwise                  = do
      (delta, Destr {typ = etyp, args = eargs}) <- existentialize ann d
      ctx' <- withCtx (const delta) $ branch $ etyp `subtypeOf` expected
      foldlM folder ctx' $ zip pats eargs
      where
        folder acc (p, t) = do
          t' <- substCtx acc t `decorateErr` (Other $ show $ "substCtx" <+> pretty acc <+> pretty t)
          withCtx (const acc) $ checkPat p t'