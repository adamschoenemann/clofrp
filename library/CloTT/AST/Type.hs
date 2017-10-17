
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

module CloTT.AST.Type where

import CloTT.Annotated 
import CloTT.AST.Name
import CloTT.AST.Kind

import Data.String (IsString(..))
import qualified Data.Set as S
import Data.Data (Data, Typeable)
import Data.Char (isUpper)
import Data.Text.Prettyprint.Doc

type Type a s = Annotated a (Type' a s)

data TySort = Mono | Poly deriving (Show, Eq)

data Type' :: * -> TySort -> * where
  TFree   :: Name                        -> Type' a s
  TVar    :: Name                        -> Type' a s
  TExists :: Name                        -> Type' a s
  TApp    :: Type a s     -> Type a s    -> Type' a s
  (:->:)  :: Type a s     -> Type a s    -> Type' a s
  Forall  :: Name -> Kind -> Type a Poly -> Type' a Poly
  Clock   :: Name         -> Type a Poly -> Type' a Poly
  RecTy   :: Type a s                    -> Type' a s
  TTuple  :: [Type a s]                  -> Type' a s


deriving instance Eq a       => Eq (Type' a s)
deriving instance Data a     => Data (Type' a Poly)
deriving instance Typeable a => Typeable (Type' a Poly)

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

  Clock n t -> 
    let (ns, t') = collect p t
        bound = hsep $ map pretty (n:ns)
    in  parensIf $ "∇" <> bound <> dot <+> prettyT False t'
        where
          p :: Type' a s -> Maybe (Name, Type a s)
          p (Clock n' t')  = Just (n',t')
          p _            = Nothing
  
  RecTy t -> parensIf $ "Fix" <+> prettyT False t
  TTuple ts -> parens (tupled $ map (prettyT False) ts)
  where
    collect :: Pretty n => (Type' a s -> Maybe (n, Type a s)) -> Type a s -> ([n], Type a s)
    collect p (A ann ty')
      | Just (n, t) <- p ty' = 
          let (ns, t') = collect p t
          in  (n:ns, t')
      | otherwise            = ([], A ann ty')

    parensIf = if pars then parens else id


prettyT :: Bool -> Type a s -> Doc ann
prettyT n (A _ t) = prettyT' n t

instance Pretty (Type' a s) where
  pretty = prettyT' False

instance Pretty (Type a s) where
  pretty (A _ t) = prettyT' False t

-- instance Show (Type' a s) where
--   show = show . pretty

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
  Clock nm tau  -> Clock  nm (unannT tau)
  RecTy tau     -> RecTy  (unannT tau)
  TTuple ts     -> TTuple (map unannT ts)

deriving instance Show a => Show (Type' a s)

nameToType' :: Name -> Type' a s
nameToType' nm@(UName (c:cs)) | isUpper c = TFree nm
nameToType' nm = TVar nm

nameToExistential' :: Name -> Type' a s
nameToExistential' nm@(UName (c:cs)) | isUpper c = TFree nm
nameToExistential' nm = TExists nm

  
instance IsString (Type () s) where
  fromString [] = error "empty string not expected" 
  fromString (c:cs) 
    | isUpper c = A () . TFree . UName $ (c:cs)
    | otherwise = A () . TVar . UName  $ (c:cs)

infixl 9 @@:
(@@:) :: Type () Poly -> Type () Poly -> Type () Poly
a @@: b = A () $ a `TApp` b

infixr 2 @->:
(@->:) :: Type () s -> Type () s -> Type () s 
a @->: b = A () $ a :->: b

freeVars :: Type a s -> S.Set Name
freeVars (A _ ty) =
  case ty of
    TFree n -> S.singleton n
    TVar n  -> S.singleton n
    TExists n -> S.singleton n
    TApp x y -> freeVars x `S.union` freeVars y
    x :->: y  -> freeVars x `S.union` freeVars y
    Forall n k t -> freeVars t `S.difference` S.singleton n
    Clock  n t -> freeVars t `S.difference` S.singleton n
    RecTy  t -> freeVars t 
    TTuple ts -> S.unions $ map freeVars ts

inFreeVars :: Name -> Type a s -> Bool
inFreeVars nm t = nm `S.member` freeVars t

iterType :: (Type a Poly -> Type a Poly) -> (Type a Poly -> Type a Poly) -> Type a Poly -> Type a Poly
iterType base go ty@(A ann ty') = 
  case ty' of
    TFree n -> base ty
    TVar n  -> base ty
    TExists n -> base ty
    TApp x y   -> A ann $ TApp (go x) (go y)
    x :->: y   -> A ann $ go x :->: go y
    Forall n k t -> A ann $ Forall n k (go t)
    Clock  n t -> A ann $ Clock  n (go t)
    RecTy  t -> A ann $ RecTy (go t)
    TTuple ts -> A ann $ TTuple (map go ts)

-- asPolytype' :: Type a s -> Type a Poly
asPolytype :: Type a s -> Type a Poly
asPolytype (A a ty) = A a $ 
  case ty of
    TFree x      -> TFree x
    TVar x       -> TVar x
    TExists x    -> TExists x
    t1 `TApp` t2 -> asPolytype t1 `TApp` asPolytype t2
    t1 :->:    t2 -> asPolytype t1 :->: asPolytype t2
    Forall x k t  -> Forall x k (asPolytype t) 
    Clock  x t   -> Clock  x (asPolytype t) 
    RecTy  t     -> RecTy (asPolytype t) 
    TTuple ts    -> TTuple (map asPolytype ts)

asMonotype :: Type a s -> Maybe (Type a Mono)
asMonotype (A a ty) = 
  case ty of
    TFree x -> pure (A a $ TFree x)
    TVar  x -> pure (A a $ TVar x)

    TExists x -> pure (A a $ TExists x)

    t1 `TApp` t2 -> (\x y -> A a $ TApp x y) <$> asMonotype t1 <*> asMonotype t2
    
    t1 :->: t2 -> (\x y -> A a (x :->: y)) <$> asMonotype t1 <*> asMonotype t2
    
    Forall _ _ _ -> Nothing

    -- TODO: Are clock quantifiers monotypes?
    Clock  _ _ -> Nothing

    RecTy  t -> A a . RecTy <$> asMonotype t

    TTuple ts -> A a . TTuple <$> sequence (map asMonotype ts)

subst :: Type a Poly -> Name -> Type a Poly -> Type a Poly
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

    Clock  y t  | y == forY -> A a $ Clock y t 
                | otherwise -> A a $ Clock y (subst x forY t)

    RecTy  t  -> A a $ RecTy (subst x forY t)
    TTuple ts -> A a $ TTuple (map (subst x forY) ts)

    t1 `TApp` t2 -> A a $ subst x forY t1 `TApp` subst x forY t2
    
    t1 :->: t2 -> A a $ subst x forY t1 :->: subst x forY t2