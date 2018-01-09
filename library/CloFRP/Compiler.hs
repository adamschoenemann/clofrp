{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleContexts #-}

-- compile CloFRP programs to Haskell (denotational semantics)
module CloFRP.Compiler where

import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Syntax (Q, Dec)
import Language.Haskell.TH.Lib
import Data.Function (fix)
import Data.Maybe (mapMaybe)
import Data.Functor.Classes

import CloFRP.AST hiding (match, Prim(..))
import qualified CloFRP.AST.Prim as P
import CloFRP.Annotated
import CloFRP.Pretty

data ClockKind = K0

unguard :: ((() -> a) -> a) -> a -> a
unguard f x = f (\_ -> x)

gfix :: ((() -> a) -> a) -> a
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

delay :: () -> a -> a
delay !u a = a

nameToName :: Name -> TH.Name
nameToName = TH.mkName . show

progToHaskDecls :: Prog a -> Q [Dec]
progToHaskDecls (Prog decls) = sequence (mapMaybe declToHaskDecl decls) where
  declToHaskDecl decl@(A _ decl') = 
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
dtToHaskDt (Datatype {dtName = nm, dtExtern = ex, dtBound = b, dtConstrs = cs, dtDeriving = ds})
  | ex = Nothing -- extern data-types does not generate Haskell syntax
  | otherwise = Just $ dataD ctx (nameToName nm) bound kind constrs derivs where
      ctx = pure []
      bound = bndrsToHaskBndrs b
      kind  = Nothing
      constrs = map constrToHaskConstr cs
      derivs = map derivToHaskDeriv ds

derivToHaskDeriv :: String -> DerivClauseQ
derivToHaskDeriv clazz = derivClause Nothing [conT (TH.mkName clazz)]

constrToHaskConstr :: Constr a -> ConQ
constrToHaskConstr (A _ (Constr nm args)) = normalC (nameToName nm) (map argToBangTypeQ args) where
  argToBangTypeQ typ =
    bangType (bang noSourceUnpackedness sourceStrict) (typeToHaskType typ)

typeToHaskType :: PolyType a -> TypeQ
typeToHaskType = go where
  go (A _ typ') = case typ' of
    TFree x       -> conT (nameToName x)
    TVar x        -> varT (nameToName x)
    TExists x     -> error $ "cannot compile existential " ++ show x
    t1 `TApp` t2  -> appT (go t1) (go t2)
    t1 :->: t2    -> arrowT `appT` go t1 `appT` go t2
    Forall nm k tau -> forallT [kindedTV (nameToName nm) (kindToHaskKind k)] (pure []) (go tau)
    RecTy tau     -> conT ''Fix `appT` go tau
    TTuple ts     -> foldl (\acc x -> acc `appT` go x) (tupleT (length ts)) ts
    Later x t     -> arrowT `appT` conT ''() `appT` go t

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
      | isConstrNm nm  -> conE (nameToName nm)
      | otherwise      -> varE (nameToName nm)
    TickVar nm         -> varE (nameToName nm)
    Ann e t            -> go e 
    App e1 e2          -> [|$(go e1) $(go e2)|]
    Lam nm mty e       -> lamE [bangP . varP $ nameToName nm] (go e)
    TickAbs nm kappa e -> lamE [bangP . varP $ nameToName nm] (go e)
    Tuple es           -> tupE (map go es)
    Let p e1 e2        -> letE [valD (patToHaskPatQ p) (normalB (exprToHaskExpQ e1)) []] (go e2)
    Case e clauses     -> caseE (go e) (clausesToMatchQ clauses)
    TypeApp e t        -> go e
    Fmap t             -> varE 'fmap
    PrimRec t          -> varE 'primRec
    BinOp nm e1 e2     -> [| $(varE $ nameToName nm) $(go e1) $(go e2) |]
    Prim p             -> primToHaskExprQ p

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
  P.PntrDeref p    -> error "cannot compile PntrDeref"


-- termToHaskExpQ :: Term a -> ExpQ
-- termToHaskExpQ term = go term where
--   go = \case
--     TmFst a t                    -> [|fst $(go t)|]
--     TmSnd a t                    -> [|snd $(go t)|]
--     TmTup a t1 t2                -> [|($(go t1), $(go t2))|]
--     TmInl a t                    -> [|Left  $(go t)|]
--     TmInr a t                    -> [|Right $(go t)|]
--     TmCase a t (ln, lt) (rn, rt) ->
--         [| case $(go t) of
--              Left  $(varP (mkName ln)) -> $(go lt)
--              Right $(varP (mkName rn)) -> $(go rt)
--         |]
--     TmLam a nm mty t             -> lamE [bangP . varP $ mkName nm] (go t)
--     TmVar a nm                   -> varE (mkName nm)
--     TmApp a  t1 t2               -> [|$(go t1) $(go t2)|]
--     TmCons a t1 t2               -> conE (mkName ":") `appE` go t1 `appE` go t2 -- [|$(go t1) : $(go t2)|]
--     TmOut a  _ t                 -> [|out $(go t)|]
--     TmInto a _ t                 -> [|Into $(go t)|]
--     TmStable a t                 -> go t
--     TmDelay a t1 t2              -> go t2 -- varE 'delay `appE` go t1 `appE` go t2
--     TmPromote a t                -> go t
--     TmLet a pat t1 t2            -> letE [patToHaskDecQ pat t1] (go t2)
--     TmLit a l                    -> case l of
--       LNat x                     -> litE (integerL (toInteger x))
--       LBool True                 -> conE 'True
--       LBool False                -> conE 'False
--       LUnit                      -> conE '()
--       LUndefined                 -> varE (mkName "undefined")
--     TmBinOp a op t1 t2           -> [| $(varE $ mkName (ppshow op)) $(go t1) $(go t2) |]
--     TmITE a b tt tf              -> [|if $(go b) then $(go tt) else $(go tf)|]
--     TmPntr a lbl                 -> undefined
--     TmPntrDeref a lbl            -> undefined
--     TmInput a nm                 -> undefined
--     TmAlloc a                    -> conE '()
--     TmFix a nm mty t             -> (varE 'fix) `appE` (lamE [varP $ mkName nm] (go t))


