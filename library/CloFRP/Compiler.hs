{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}

-- compile CloFRP programs to Haskell (denotational semantics)
module CloFRP.Compiler where

import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Syntax (Q, Dec)
import Language.Haskell.TH.Lib
import Data.Maybe (mapMaybe)
import Data.Functor.Classes

import CloFRP.AST hiding (match, Prim(..))
import qualified CloFRP.AST.Prim as P
import CloFRP.Annotated

data ClockKind = K0

type Later (k :: ClockKind) a = () -> a

data StreamF' (k :: ClockKind) a f = Cons' !a !(Later k f) deriving Functor

unguard :: ((() -> a) -> a) -> a -> a
unguard f x = f (\_ -> x)

gfix :: (Later k a -> a) -> a
gfix f = -- fix (unguard f)
  let x = f (\_ -> x)
  in  x

-- F[μX. F[X]] -> (μX. F[X])
data Fix f = Fold (f (Fix f))

instance Show1 f => Show (Fix f) where
  showsPrec d (Fold a) =
    showParen (d >= 11)
      $ showString "Fold "
      . showsPrec1 11 a

-- (μX. F[X]) -> F[μX. F[X]]
unfold :: Fix f -> f (Fix f)
unfold (Fold f) = f

-- primitive recursion
-- (F[(µX. F) × A] → A) → µX. F[X] → A
primRec :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
primRec fn (Fold f) =
  fn (fmap (\y -> (y, primRec fn y)) f)

nameToName :: Name -> TH.Name
nameToName = TH.mkName . show

progToHaskDecls :: Prog a -> Q [Dec]
progToHaskDecls (Prog decls) = sequence (mapMaybe declToHaskDecl decls) where
  declToHaskDecl (A _ decl') =
    case decl' of
      FunD nm e    -> Just $ valD (varP (nameToName nm)) (normalB $ exprToHaskExpQ e) []
      SigD nm ty   -> Just $ sigD (nameToName nm) (typeToHaskType ty)
      DataD dt     -> dtToHaskDt dt
      SynonymD syn -> Just $ synToHaskSyn syn

synToHaskSyn :: Synonym a -> DecQ
synToHaskSyn (Synonym {synName = nm, synBound = bnd, synExpansion = ex}) =
  tySynD (nameToName nm) (bndrsToHaskBndrs bnd) (typeToHaskType ex)

bndrsToHaskBndrs :: [(Name, Kind)] -> [TH.TyVarBndr]
bndrsToHaskBndrs = map (\(n,k) -> kindedTV (nameToName n) (kindToHaskKind k))

dtToHaskDt :: Datatype a -> Maybe DecQ
dtToHaskDt (Datatype { dtName = nm, dtExtern = ex, .. })
  | ex = Nothing -- extern data-types does not generate Haskell syntax
  | otherwise = Just $ dataD ctx (nameToName nm) bound kind constrs derivs where
      ctx = pure []
      bound = bndrsToHaskBndrs dtBound
      kind  = Nothing
      constrs = map constrToHaskConstr dtConstrs
      derivs = map derivToHaskDeriv dtDeriving

derivToHaskDeriv :: String -> DerivClauseQ
derivToHaskDeriv clazz = derivClause Nothing [conT (TH.mkName clazz)]

constrToHaskConstr :: Constr a -> ConQ
constrToHaskConstr (A _ (Constr nm args)) = normalC (nameToName nm) (map argToBangTypeQ args) where
  argToBangTypeQ typ =
    bangType (bang noSourceUnpackedness sourceStrict) (typeToHaskType typ)

typeToHaskType :: PolyType a -> TypeQ
typeToHaskType = go where
  go (A _ typ') = case typ' of
    TFree x       -> conT (nameToName x)                  -- ⟦𝒯⟧ = 𝒯
    TVar x        -> varT (nameToName x)                  -- ⟦x⟧ = x
    TExists x     -> error $ "cannot compile existential " ++ show x
    t1 `TApp` t2  -> go t1 `appT` go t2                   -- ⟦t1 t2⟧ = ⟦t1⟧ ⟦t2⟧
    t1 :->: t2    -> arrowT `appT` go t1 `appT` go t2     -- ⟦t1 -> t2⟧ = ⟦t1⟧ -> ⟦t2⟧
    Forall nm k tau ->                                    -- ⟦forall (a : k). t⟧ = forall (a :: k) ⟦t⟧
      let b = kindedTV (nameToName nm) (kindToHaskKind k)
      in  forallT [b] (pure []) (go tau)
    RecTy tau     -> conT ''Fix `appT` go tau             -- ⟦Fix t⟧ = Fix ⟦t⟧
    TTuple ts     ->                                      -- ⟦(t1, ..., tn)⟧ = (⟦t1⟧, ..., ⟦tn⟧)
      foldl (\acc x -> acc `appT` go x) (tupleT (length ts)) ts
    Later k t     -> conT ''Later `appT` go k `appT` go t -- ⟦▷k t⟧ = Later ⟦k⟧ ⟦t⟧

kindToHaskKind :: Kind -> TH.Kind
kindToHaskKind = go where
  go = \case
    Star -> starK
    k1 :->*: k2 -> arrowK `appK` go k1 `appK` go k2
    ClockK -> conK ''ClockKind


exprToHaskExpQ :: Expr a -> ExpQ
exprToHaskExpQ = go where
  go (A _ expr') = case expr' of
    Var nm
      | isConstrNm nm  -> conE (nameToName nm)               -- ⟦𝒞⟧ = 𝒞
      | otherwise      -> varE (nameToName nm)               -- ⟦x⟧ = x
    TickVar nm         -> varE (nameToName nm)               -- ⟦[x]⟧ = x
    Ann e t            -> sigE (go e) (typeToHaskType t)     -- ⟦e : t⟧ = e :: t
    App e1 e2          -> appE (go e1) (go e2)               -- ⟦e1 e2⟧ = ⟦e1⟧ ⟦e2⟧
    Lam nm mty e       ->                                    -- ⟦λ(x : t). e⟧ = λ(!x :: ⟦t⟧). ⟦e⟧
      lamE [lamArg (nameToName nm) (typeToHaskType <$> mty)] (go e)
    TickAbs nm kappa e ->                                    -- ⟦γ(x : k). e⟧ = λ!x. ⟦e⟧
      lamE [lamArg (nameToName nm) (Just $ conT ''())] (go e)
    Tuple es           -> tupE (map go es)                   -- ⟦(e₁, ..., eₙ)⟧ = (⟦e₁⟧, ..., ⟦eₙ⟧)
    Let p e1 e2        ->                                    -- ⟦let p = e1 in e2⟧ = let ⟦p⟧ = ⟦e1⟧ in ⟦e2⟧
      let clause = valD (patToHaskPatQ p) (normalB (exprToHaskExpQ e1)) []
      in  letE [clause] (go e2)
    Case e clauses     ->                                    -- ⟦case e of cs⟧ = case ⟦e⟧ of ⟦cs⟧
      caseE (go e) (clausesToMatchQ clauses)
    TypeApp e t        -> appTypeE (go e) (typeToHaskType t) -- ⟦e {t}⟧ = ⟦e⟧ @⟦t⟧
    Fmap t             -> varE 'fmap                         -- ⟦$\mathtt{fmap}_F$⟧ = fmap
    PrimRec t          -> varE 'primRec                      -- ⟦primRec⟧ = primRec
    BinOp nm e1 e2     ->                                    -- ⟦op e1 e2⟧ = (⟦op⟧) ⟦e1⟧ ⟦e2⟧
      varE (nameToName nm) `appE` go e1 `appE` go e2
    Prim p             -> primToHaskExprQ p

  lamArg nm mty =
    maybe (bangP (varP nm)) (bangP . sigP (varP nm)) mty

clausesToMatchQ :: [(Pat a, Expr a)] -> [MatchQ]
clausesToMatchQ = foldr clauseToMatchQ [] where
  clauseToMatchQ (p, e) acc = match (patToHaskPatQ p) (normalB (exprToHaskExpQ e)) [] : acc

patToHaskPatQ :: Pat a -> PatQ
patToHaskPatQ  = go where
  go (A _ pat') = case pat' of
    Bind nm -> varP (nameToName nm)
    Match nm pats -> conP (nameToName nm) (map go pats)
    PTuple ps -> tupP (map go ps)

primToHaskExprQ :: P.Prim -> ExpQ
primToHaskExprQ = \case
  P.Unit           -> conE '()
  P.Integer x      -> litE (integerL x)
  P.Fold           -> conE 'Fold
  P.Unfold         -> varE 'unfold
  P.Tick           -> conE '()
  P.Fix            -> varE 'gfix
  P.Undefined      -> varE 'undefined
  P.Input          -> error "cannot compile Input"
