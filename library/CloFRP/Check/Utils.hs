{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CloFRP.Check.Utils where

import Data.Foldable (foldrM, find)
import Data.Maybe (isJust)
import Data.List (genericLength)

import CloFRP.Check.TypingM 
import CloFRP.Check.Destr (Destr(..))
import CloFRP.Check.Contexts ( LocalCtx(..), CtxElem(..), (<+), isInContext
                             , Context(..), ctxFind, findAssigned, insertAt'
                             , splitCtx', before', Binding(..)
                             )
import CloFRP.AST.Type (Type'(..), subst, PolyType, MonoType, asPolytype)
import CloFRP.AST.Kind (Kind(..))
import CloFRP.AST.Name (Name(..))
import CloFRP.AST.Pat (Pat, Pat'(..))
import CloFRP.Annotated (Annotated(..), (=%=), unann)
import CloFRP.Pretty

-- | Take a destructor and "existentialize it" - replace its bound type-variables
-- with fresh existentials
existentialize :: a -> Destr a -> TypingM a (LocalCtx a, Destr a)
existentialize ann destr = do
  (nms, destr') <- foldrM folder ([], destr) (bound destr)
  ctx <- getCtx
  let ctx' = foldr (\(n,k) g -> g <+ Exists n k) ctx nms
  pure (ctx', destr')
  where
    folder (b,k) (nms, d@(Destr {typ, args})) = do
      b' <- freshName
      let s = subst (A ann $ TExists b') b
      let ntyp = s typ
      let nargs = map s args
      pure $ ((b',k) : nms, d {typ = ntyp, args = nargs})

-- | Check that a type is well-formed.
checkWfType :: PolyType a -> TypingM a ()
checkWfType ty = kindOf ty *> pure ()

kindOf :: PolyType a -> TypingM a Kind
kindOf ty = go ty `decorateErr` decorate where
  go (A _ t) = do
    kctx <- getKCtx
    ctx <- getCtx
    case t of
      TFree v -> maybe (freeNotFound v) pure $ query v kctx
      TVar v -> queryKind v
      TExists  v -> queryKind v

      TApp t1 t2 -> do
        k1 <- go t1
        k2 <- go t2
        case (k1, k2) of
          (k11 :->*: k12, k2')
            | k11 == k2' -> pure k12
            | otherwise  ->
                otherErr $ "Expected " ++ pps t2 ++ " to have kind " ++ pps k11
          (_k1', _) -> otherErr $ "Expected " ++ pps t1 ++ " to be a type constructor"

      t1 :->: t2 -> do
        k1 <- go t1
        k2 <- go t2
        case (k1, k2) of
          (Star, Star) -> pure Star
          (k1', k2')   -> otherErr $ "Both operands in arrow types must have kind *, but had "
                      ++ pps k1' ++ " and " ++ pps k2' ++ " in " ++ pps t

      Forall v k tau -> do
        errIf (isInContext (Uni v k) <$> getCtx) (/= False) (\_ -> Other $ show $ pretty v <+> "is already universally quantified")
        withCtx (\g -> g <+ Uni v k) $ go tau

      RecTy tau -> do
        k <- go tau
        case k of
          Star :->*: k' -> pure k'
          _            -> otherErr $ show $ pretty tau <+> "must have kind * -> k to be an argument to Fix"

      TTuple ts -> (traverse fn ts) *> pure Star where
        fn tt = kindOf tt >>= \case
          Star -> pure ()
          k    -> otherErr $ show $ pretty tt <+> "must have kind * but had kind" <+> pretty k

      Later k tau -> do
        k' <- go tau
        case k' of
          Star -> pure Star
          _    -> otherErr $ show $ pretty tau <+> "must have kind * at" <+> pretty ty <+> "but had kind" <+> pretty k'

    where
      freeNotFound v = do
        kctx <- getKCtx
        nameNotFound v `decorateErr` (Other $ show $ "looking up a free variable in kind-ctx" <+> pretty kctx)

  decorate = Other $ show $ "kindOf" <+> (pretty ty)

queryKind :: Name -> TypingM a Kind
queryKind nm = do
  ctx <- getCtx
  case ctxFind p ctx of
    Just (Exists _ k) -> pure k
    Just (Uni _ k)    -> pure k
    Just (_ := ty)    -> kindOf (asPolytype ty) `decorateErr` Other ("queryKind")
    _                 -> 
      otherErr $ showW 3000 $ "queryKind: Cannot lookup kind of" <+> 
      pretty nm <+> "in" <+> pretty ctx
  where
      p (Uni x _)    = x == nm
      p (Exists x _) = x == nm
      p (x := _)     = x == nm
      p _             = False

-- | Assign an unsolved variable to a type in a context
-- TODO: Optimize
assign :: Name -> MonoType a -> TypingM a (LocalCtx a)
assign nm ty = do
  ctx@(LocalCtx xs) <- getCtx
  case findAssigned nm ctx of
    Just ty'
      | ty =%= ty' -> pure ctx
      | otherwise  -> otherErr $ show $ pretty nm
                  <+> "is already assigned to" <+> pretty ty'
    Nothing ->
       foldrM fn ([], False) xs >>= \case
        (xs', True) -> do
          let asserr = Other $ show $ "Assigning" <+> pretty nm <+> "to"
                    <+> pretty ty
          _ <- wfContext (LocalCtx xs') `decorateErr` asserr
          pure (LocalCtx xs')
        (xs', False) -> otherErr $ show $ pretty nm <+> ":=" <+> pretty ty <+> "Didn't assign anything"
      where
        fn (Exists nm' k) (xs', _) | nm == nm' = do 
          tyk <- kindOf $ asPolytype ty
          if (tyk /= k)
            then otherErr $ show $ "Expected" <+> pretty ty <+> "to have kind" 
                 <+> pretty k <+> "but it had kind" <+> pretty tyk
            else pure (nm := ty : xs', True)
        fn x (xs', b)                          = pure (x : xs', b)

wfContext :: forall a. LocalCtx a -> TypingM a ()
wfContext (LocalCtx elems) = (foldrM folder [] elems *> pure ())  where
  folder :: CtxElem a -> [CtxElem a] -> TypingM a [CtxElem a]
  folder el acc = do
    _ <- withCtx (const $ LocalCtx acc) $ checkIt el
    pure (el : acc)

  elem' f xs = isJust $ find (\x -> f (unann x)) xs

  -- this one refers to ctx through getCtx
  checkIt el = case el of
    Uni nm _        -> notInDom nm el
    Exists nm _     -> notInDom nm el
    (_, nm) `HasType` ty -> notInDom nm el *> checkWfType (asPolytype ty) `decorateErr` (NotWfContext el)
    nm := ty        -> notInDom nm el *> checkWfType (asPolytype ty) `decorateErr` (NotWfContext el)
    Marker nm       -> do
      _ <- notInDom nm el
      LocalCtx ctx <- getCtx
      if ((\x -> Marker nm == x) `elem'` ctx)
        then notWfContext (Marker nm)
        else pure ()

  -- TODO: fix this to account for HasType constructor as well
  notInDom nm el = do
    ctx <- getCtx
    if (isJust $ ctxFind p ctx)
      then notWfContext el
      else pure ()
    where
      p (Uni x _)    = x == nm
      p (Exists x _) = x == nm
      p (x := _)     = x == nm
      p _            = False

insertAt :: CtxElem a -> LocalCtx a -> TypingM a (LocalCtx a)
insertAt at insertee = do
  ctx <- getCtx
  case insertAt' at insertee ctx of
    Nothing   -> otherErr $ show $ "Cannot insert" <+> pretty insertee <+> "into context" <+> pretty ctx <+> "at" <+> pretty at
    Just ctx' -> pure ctx'

splitCtx :: CtxElem a -> LocalCtx a -> TypingM a (LocalCtx a, CtxElem a, LocalCtx a)
splitCtx el ctx =
  case splitCtx' el ctx of
    Nothing -> root "splitCtx" *> cannotSplit el ctx
    Just x  -> pure x

-- | Check if a context element occurs before another
-- context element in the current context
before :: CtxElem a -> CtxElem a -> TypingM a Bool
before alpha beta = before' alpha beta <$> getCtx
