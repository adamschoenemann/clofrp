{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}

module CloFRP.Check.Instantiation where

import Control.Monad.Error (throwError, catchError)
import Data.Foldable (foldrM)

import CloFRP.AST.Name
import CloFRP.AST.Type
import CloFRP.AST.Kind
import CloFRP.Check.TypingM
import CloFRP.Check.Contexts
import CloFRP.Annotated (Annotated(..))
import CloFRP.Pretty
import CloFRP.Check.Utils 


solve :: Name -> Type a s -> TypingM a (LocalCtx a)
solve ahat ty = do
  mty <- asMonotypeTM ty
  assign ahat mty

-- | Under input context Γ, instantiate α^ such that α^ <: A, with output context ∆
-- TODO: Find a way to abstract all these near-identical definitions out. Also, combine instL and instR, or
-- at least implement them both in terms of a more general combinator
instL :: Name -> PolyType a -> TypingM a (LocalCtx a)
-- InstLSolve
instL ahat ty@(A a ty') =
  (solve ahat ty <* rule "InstLSolve" (pretty ahat <+> ":<=" <+> pretty ty)) `catchError` \err ->
      case ty' of
        -- InstLReach
        TExists bhat -> do
          ak <- queryKind ahat
          bk <- queryKind bhat
          rule "InstLReach" ("^" <> pretty bhat <+> "=" <+> "^" <> pretty ahat)
          Exists ahat ak `before` Exists bhat bk >>= \case
            True -> assign bhat (A a $ TExists ahat)
            False -> otherErr $ "[InstLReach] error"

        -- InstLArr
        t1 :->: t2 -> do
          rule "InstLArr" (pretty ahat <+> ":<=" <+> pretty ty)
          af1 <- freshName
          af2 <- freshName
          let ahat1 = Exists af1 Star
          let ahat2 = Exists af2 Star
          let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
          ctx' <- insertAt (Exists ahat Star) [ahat2, ahat1, ahat := arr]
          omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
          substed <- substCtx omega t2
          withCtx (const omega) $ branch (af2 `instL` substed)

        -- InstLAllR
        Forall beta k bty -> do
          rule "InstLAllR" (pretty ahat <+> ":<=" <+> pretty ty)
          beta' <- freshName
          let bty' = subst (A a $ TVar beta') beta bty
          theta <- withCtx (\g -> g <+ Uni beta' k) $ branch (ahat `instL` bty')
          pure $ dropTil (Uni beta' k) theta

        -- InstLTApp. Identical to InstLArr
        TApp t1 t2 -> do
          rule "InstLTApp" (pretty ahat <+> ":<=" <+> pretty ty)
          af1 <- freshName
          af2 <- freshName
          t1k <- kindOf t1
          t2k <- kindOf t2
          tyk <- kindOf ty
          let expectKind = t2k :->*: tyk
          errIf (pure t1k) (/= expectKind) (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected" <+> pretty expectKind)
          let ahat1 = Exists af1 t1k
          let ahat2 = Exists af2 t2k
          let app = A a $ (A a $ TExists af1) `TApp` (A a $ TExists af2)
          ctx' <- insertAt (Exists ahat tyk) [ahat2, ahat1, ahat := app]
          omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
          substed <- substCtx omega t2
          withCtx (const omega) $ branch (af2 `instL` substed)

        -- InstLTuple
        TTuple ts -> do
          rule "InstLTuple" (pretty ty <+> "=<:" <+> pretty ahat)
          nms <- traverse (const freshName) ts
          tyk <- kindOf ty
          let existstup = A a $ TTuple $ map (A a . TExists) nms
          ctx' <- insertAt (Exists ahat tyk) (foldr (\x g -> g <+ Exists x Star) mempty nms <+ ahat := existstup)
          foldrM folder ctx' $ zip nms ts
          where
            folder (af, t) acc = do
              tsubst <- substCtx acc t
              branch $ withCtx (const acc) $ tsubst `instR` af

        -- InstLLater. Similar to instantiation of other type-combinators
        Later t1 t2 -> do
          rule "InstLLater" (pretty ahat <+> ":<=" <+> pretty ty)
          af1 <- freshName
          af2 <- freshName
          errIf (kindOf t1) (/= ClockK) (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected Clock")
          errIf (kindOf t2) (/= Star)   (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected *")
          let ahat1 = Exists af1 ClockK
          let ahat2 = Exists af2 Star
          let ltr = A a $ Later (A a $ TExists af1) (A a $ TExists af2)
          ctx' <- insertAt (Exists ahat Star) [ahat2, ahat1, ahat := ltr]
          omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
          substed <- substCtx omega t2
          r <- withCtx (const omega) $ branch (af2 `instL` substed)
          pure r

        -- InstLRec
        RecTy t -> do
          rule "InstLRec" (pretty ahat <+> ":<=" <+> pretty ty)
          a1 <- freshName
          let rt = A a $ RecTy (A a $ TExists a1)
          k <- kindOf t
          ctx' <- insertAt (Exists ahat Star) [Exists a1 k, ahat := rt]
          withCtx (const ctx') $ branch (a1 `instL` t)

        _ -> do
          rule "InstLError" ("^" <> pretty ahat <+> "=" <+> pretty ty)
          throwError err

-- | Under input context Γ, instantiate α^ such that α^ >: A, with output context ∆
instR :: PolyType a -> Name -> TypingM a (LocalCtx a)
-- InstRSolve
instR ty@(A a ty') ahat =
  (solve ahat ty <* rule "InstRSolve" (pretty ty <+> "=<:" <+> pretty ahat)) `catchError` \err ->
        case ty' of
          -- InstRReach
          TExists bhat -> do
            ak <- queryKind ahat
            bk <- queryKind bhat
            rule "InstRReach" ("^" <> pretty ahat <+> "=" <+> "^" <> pretty bhat)
            Exists ahat ak `before` Exists bhat bk >>= \case
              True -> assign bhat (A a $ TExists ahat)
              False -> otherErr $ "[InstRReachError]"

          -- InstRArr
          t1 :->: t2 -> do
            rule "InstRArr" (pretty ty <+> "=<:" <+> pretty ahat)
            af1 <- freshName
            af2 <- freshName
            let ahat1 = Exists af1 Star
            let ahat2 = Exists af2 Star
            let arr = A a $ (A a $ TExists af1) :->: (A a $ TExists af2)
            ctx' <- insertAt (Exists ahat Star) [ahat2, ahat1, ahat := arr]
            omega <- withCtx (const ctx') $ branch (af1 `instL` t1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          -- InstRAllL
          Forall beta k bty -> do
            rule "InstRAllL" (pretty ty <+> "=<:" <+> pretty ahat)
            beta' <- freshName
            let bty' = subst (A a $ TExists beta') beta bty
            ctx' <- withCtx (\g -> g <+ marker beta' <+ Exists beta' k) $ branch (bty' `instR` ahat)
            (delta, _, _delta') <- splitCtx (Marker beta') ctx'
            pure delta

          -- InstRTApp. Identical to InstRArr
          TApp t1 t2 -> do
            rule "InstRTApp" (pretty ty <+> "=<:" <+> pretty ahat)
            af1 <- freshName
            af2 <- freshName
            t1k <- kindOf t1
            t2k <- kindOf t2
            tyk  <- kindOf ty
            let ahat1 = Exists af1 t1k
            let ahat2 = Exists af2 t2k
            let app = A a $ (A a $ TExists af1) `TApp` (A a $ TExists af2)
            ctx' <- insertAt (Exists ahat tyk) [ahat2, ahat1, ahat := app]
            omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          -- InstRRec
          RecTy t -> do
            rule "InstRRec" (pretty ty <+> "=<:" <+> pretty ahat)
            a1 <- freshName
            let rt = A a $ RecTy (A a $ TExists a1)
            k <- kindOf t
            ctx' <- insertAt (Exists ahat Star) [Exists a1 k, ahat := rt]
            withCtx (const ctx') $ branch (t `instR` a1)

          -- InstRTuple
          TTuple ts -> do
            rule "InstRTuple" (pretty ty <+> "=<:" <+> pretty ahat)
            nms <- traverse (const freshName) ts
            tyk <- kindOf ty
            let existstup = A a $ TTuple $ map (A a . TExists) nms
            ctx' <- insertAt (Exists ahat tyk) (foldr (\x g -> g <+ Exists x Star) mempty nms <+ ahat := existstup)
            foldrM folder ctx' $ zip nms ts
            where
              folder (af, t) acc = do
                tsubst <- substCtx acc t
                branch $ withCtx (const acc) $ af `instL` tsubst

          -- InstRLater. Similar to instantiation of other type-combinators
          Later t1 t2 -> do
            rule "InstRLater" (pretty ty <+> "=<:" <+> pretty ahat)
            af1 <- freshName
            af2 <- freshName
            errIf (kindOf t1) (/= ClockK) (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected Clock")
            errIf (kindOf t2) (/= Star)   (\k -> Other $ show $ pretty t1 <+> "had kind" <+> pretty k <+> "but expected *")
            let ahat1 = Exists af1 ClockK
            let ahat2 = Exists af2 Star
            let ltr = A a $ Later (A a $ TExists af1) (A a $ TExists af2)
            ctx' <- insertAt (Exists ahat Star) [ahat2, ahat1, ahat := ltr]
            omega <- withCtx (const ctx') $ branch (t1 `instR` af1)
            substed <- substCtx omega t2
            r <- withCtx (const omega) $ branch (substed `instR` af2)
            pure r

          _ -> do
            rule "InstRError" ("^" <> pretty ahat <+> "=" <+> pretty ty)
            throwError err
            -- otherErr $ showW 80 $ "[instR] Cannot instantiate" <+> pretty ahat <+> "to" <+> pretty ty <+> ". Cause:" <+> fromString err
