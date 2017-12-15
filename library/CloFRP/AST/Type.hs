
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module CloFRP.AST.Type where

import Data.String (IsString(..))
import qualified Data.Set as S
import Data.Data (Data, Typeable)
import Data.Char (isUpper)
import CloFRP.Pretty
import Control.DeepSeq

import CloFRP.Annotated
import CloFRP.AST.Name
import CloFRP.AST.Kind
import CloFRP.AST.Utils

type Type a s = Annotated a (Type' a s)

data TySort = Mono | Poly deriving (Show, Eq)

data Type' :: * -> TySort -> * where
  TFree   :: Name                         -> Type' a s -- ℱ
  TVar    :: Name                         -> Type' a s -- x
  TExists :: Name                         -> Type' a s -- α^
  TApp    :: Type a s     -> Type a s     -> Type' a s -- F B
  (:->:)  :: Type a s     -> Type a s     -> Type' a s -- A -> B
  Forall  :: Name -> Kind -> Type a 'Poly -> Type' a 'Poly -- ∀(α : χ). A
  RecTy   :: Type a s                     -> Type' a s -- Fix F
  TTuple  :: [Type a s]                   -> Type' a s -- ⟨A₁,...,Aₙ⟩
  Later   :: Type a s     -> Type a s     -> Type' a s -- ⊳k A



deriving instance Eq a       => Eq (Type' a s)
deriving instance Data a     => Data (Type' a 'Poly)
deriving instance Typeable a => Typeable (Type' a 'Poly)
-- deriving instance Show a => Show (Type' a s)

instance NFData a => NFData (Type' a 'Poly) where
  rnf a = seq a ()

prettyBound :: Bool -> Name -> Kind -> Doc ann
prettyBound _ nm Star = pretty nm
prettyBound p nm k    = (if p then parens else id) $ pretty nm <+> ":" <+> pretty k

prettyT' :: Bool -> Type' a s -> Doc ann
prettyT' pars = \case
  TFree n    -> fromString . show $ n
  TVar n     -> fromString . show $ n
  TExists n  -> "∃" <> fromString (show n)
  TApp x y   -> parensIf $ prettyT False x <+> prettyT True y
  x :->: y   -> parensIf $ prettyT True x  <> softline <> "->" <+> prettyT False y

  Forall n k t ->
    let (ns, t') = collect p t
        bound = hsep $ map (uncurry $ prettyBound True) ((n,k):ns)
    in  parensIf $ "∀" <> bound <> dot <+> prettyT False t'
        where
          p :: Type' a s -> Maybe ((Name, Kind), Type a s)
          p (Forall n' k' t') = Just ((n', k'), t')
          p _              = Nothing

  RecTy t -> parensIf $ "Fix" <+> prettyT True t
  TTuple ts -> tupled $ map (prettyT False) ts
  Later t1 t2 -> parensIf $ "⊳" <> prettyT True t1 <+> prettyT True t2
  where
    parensIf = if pars then parens else id



prettyT :: Bool -> Type a s -> Doc ann
prettyT n (A _ t) = prettyT' n t

instance Pretty (Type' a s) where
  pretty = prettyT' False

instance Pretty (Type a s) where
  pretty (A _ t) = prettyT' False t

instance Show (Type' a s) where
  show = ppsw 1000

instance Unann (Type a s) (Type () s) where
  unann = unannT

unannT :: Type a s -> Type () s
unannT (A _ t) = A () $ unannT' t

instance Unann (Type' a s) (Type' () s) where
  unann = unannT'

unannT' :: Type' a s -> Type' () s
unannT' = \case
  TFree x       -> TFree x
  TVar x        -> TVar x
  TExists x     -> TExists x
  t1 `TApp` t2  -> unannT t1 `TApp` unannT t2
  t1 :->: t2    -> unannT t1 :->: unannT t2
  Forall nm k tau -> Forall nm k (unannT tau)
  RecTy tau     -> RecTy  (unannT tau)
  TTuple ts     -> TTuple (map unannT ts)
  Later x t     -> Later (unannT x) (unannT t)


nameToType' :: Name -> Type' a s
nameToType' nm@(UName (c:_)) | isUpper c = TFree nm
nameToType' nm = TVar nm

nameToType :: a -> Name -> Type a s
nameToType ann = A ann . nameToType'

nameToExistential' :: Name -> Type' a s
nameToExistential' nm@(UName (c:_)) | isUpper c = TFree nm
nameToExistential' nm = TExists nm

instance IsString (Type () s) where
  fromString s = nameToType () (UName s)

infixl 9 @@:
(@@:) :: Type () 'Poly -> Type () 'Poly -> Type () 'Poly
a @@: b = A () $ a `TApp` b

infixr 2 @->:
(@->:) :: Type () s -> Type () s -> Type () s
a @->: b = A () $ a :->: b

-- alphaEquiv :: Type a s -> Type b s -> Bool
-- alphaEquiv t1 t2 = go (unann t1) (unann t2) 0 where
--   go (A _ t1') (A _ t2') =
--     case (t1', t2') of
--       (TFree n1, TFree n2) -> n1 == n2
--       (TVar n1, TVar n2) -> n1 == n2
--       TVar n  -> S.singleton n
--       TExists n -> S.singleton n
--       TApp x y -> freeVars x `S.union` freeVars y
--       x :->: y  -> freeVars x `S.union` freeVars y
--       Forall n k t -> freeVars t `S.difference` S.singleton n
--       RecTy  t -> freeVars t
--       TTuple ts -> S.unions $ map freeVars ts
--       Later t1 t2 -> freeVars t1 `S.union` freeVars t2

freeVars :: Type a s -> S.Set Name
freeVars (A _ ty) =
  case ty of
    TFree n -> S.singleton n
    TVar n  -> S.singleton n
    TExists n -> S.singleton n
    TApp x y -> freeVars x `S.union` freeVars y
    x :->: y  -> freeVars x `S.union` freeVars y
    Forall n _k t -> freeVars t `S.difference` S.singleton n
    RecTy  t -> freeVars t
    TTuple ts -> S.unions $ map freeVars ts
    Later t1 t2 -> freeVars t1 `S.union` freeVars t2


inFreeVars :: Name -> Type a s -> Bool
inFreeVars nm t = nm `S.member` freeVars t

asPolytype :: Type a s -> Type a 'Poly
asPolytype (A a ty) = A a $
  case ty of
    TFree x      -> TFree x
    TVar x       -> TVar x
    TExists x    -> TExists x
    t1 `TApp` t2 -> asPolytype t1 `TApp` asPolytype t2
    t1 :->:    t2 -> asPolytype t1 :->: asPolytype t2
    Forall x k t  -> Forall x k (asPolytype t)
    RecTy  t     -> RecTy (asPolytype t)
    TTuple ts    -> TTuple (map asPolytype ts)
    Later t1 t2  -> Later (asPolytype t1) (asPolytype t2)

asMonotype :: Type a s -> Maybe (Type a 'Mono)
asMonotype (A a ty) =
  case ty of
    TFree x -> pure (A a $ TFree x)
    TVar  x -> pure (A a $ TVar x)

    TExists x -> pure (A a $ TExists x)

    t1 `TApp` t2 -> (\x y -> A a $ TApp x y) <$> asMonotype t1 <*> asMonotype t2

    t1 :->: t2 -> (\x y -> A a (x :->: y)) <$> asMonotype t1 <*> asMonotype t2

    Forall _ _ _ -> Nothing

    RecTy  t -> A a . RecTy <$> asMonotype t

    TTuple ts -> A a . TTuple <$> sequence (map asMonotype ts)

    Later t1 t2 -> (\x y -> A a $ Later x y) <$> asMonotype t1 <*> asMonotype t2

subst :: Type a 'Poly -> Name -> Type a 'Poly -> Type a 'Poly
subst x forY (A a inTy) =
  case inTy of
    TFree y     | y == forY  -> x
                | otherwise -> A a $ TFree y

    TVar y      | y == forY  -> x
                | otherwise -> A a $ TVar y

    TExists y   | y == forY  -> x
                | otherwise -> A a $ TExists y

    Forall y k t  | y == forY -> A a $ Forall y k t
                  | otherwise -> A a $ Forall y k (subst x forY t)

    -- TODO: OK, this is a nasty hack to substitute clock variables
    -- will only really work as long as clock variables and type variables do not
    -- share a namespace
    Later  t1 t2  -> A a (Later (subst x forY t1) (subst x forY t2))


    RecTy  t  -> A a $ RecTy (subst x forY t)
    TTuple ts -> A a $ TTuple (map (subst x forY) ts)

    t1 `TApp` t2 -> A a $ subst x forY t1 `TApp` subst x forY t2

    t1 :->: t2 -> A a $ subst x forY t1 :->: subst x forY t2
