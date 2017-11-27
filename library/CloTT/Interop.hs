
{-|
Module      : CloTT.Interop
Description : Reflecting CloTT-Types into the Haskell type-system
-}

{-# LANGUAGE AutoDeriveTypeable  #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies  #-}

module CloTT.Interop where

import GHC.TypeLits
import           Language.Haskell.TH ( Exp (..), ExpQ, Lit (..), Pat (..), Q
                                     , DecQ, mkName, runQ)
import qualified Language.Haskell.TH.Syntax as S
import qualified Language.Haskell.TH as T
import           Data.Data

import qualified CloTT.AST as P
import           CloTT.AST (Type, TySort(..))
import           CloTT.Annotated
import           CloTT.AST.Helpers
import           CloTT.Eval
import           CloTT.Pretty

-- -----------------------------------------------------------------------------
-- CloTy
-- -----------------------------------------------------------------------------

infixr 0 :->:
infixl 9 :@:

-- | The type of CloTT-types that can be reflected
data CloTy
  = CTFree Symbol
  | CTTuple [CloTy]
  | CloTy :->: CloTy
  | CloTy :@:  CloTy
  -- deriving (Show, Eq, Typeable, Data)


-- -----------------------------------------------------------------------------
-- Sing
-- -----------------------------------------------------------------------------

-- |Singleton representation to lift Ty into types
-- using kind-promotion
data Sing :: CloTy -> * where
  SFree   :: KnownSymbol s => Proxy s -> Sing (CTFree s)
  SPair   :: Sing t1 -> Sing t2           -> Sing (CTTuple '[t1, t2])
  STup    :: Sing t  -> Sing (CTTuple ts) -> Sing (CTTuple (t ': ts))
  SApp    :: Sing t1 -> Sing t2           -> Sing (t1 :@:  t2)
  SArr    :: Sing t1 -> Sing t2           -> Sing (t1 :->: t2)

instance Show (Sing ct) where
  show x = case x of
    SFree px -> symbolVal px
    t1 `SArr` t2 -> show t1 ++ " -> " ++ show t2
    t1 `SApp` t2 -> "(" ++ show t1 ++ " " ++ show t2 ++ ")"
    t1 `SPair` t2 -> "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
    STup t ts -> 
      "(" ++ show t ++ ", " ++ tupShow ts
      where
        tupShow :: Sing (CTTuple ts') -> String
        tupShow (SPair x y) = show x ++ ", " ++ show y ++ ")"
        tupShow (STup t' ts') = show t' ++ ", " ++ tupShow ts'



deriving instance Eq (Sing a)
-- deriving instance Show (Sing a)
deriving instance Typeable (Sing a)

-- -- |Reify a singleton back into an FRP type
reifySing :: Sing t -> Type () Poly
reifySing = \case
  SFree px -> A () $ P.TFree (P.UName $ symbolVal px)
  t1 `SArr` t2 -> A () $ reifySing t1 P.:->: reifySing t2
  t1 `SApp` t2 -> A () $ reifySing t1 `P.TApp`  reifySing t2
  t1 `SPair` t2 -> A () $ P.TTuple [reifySing t1, reifySing t2]
  STup t ts ->
    A () $ P.TTuple (reifySing t : tupleSing ts)
    where
        tupleSing :: Sing (CTTuple ts') -> [Type () Poly]
        tupleSing (SPair x y) = [reifySing x, reifySing y]
        tupleSing (STup t' ts') = reifySing t' : tupleSing ts' 

infixr 0 `SArr`
infixl 9 `SApp`
infixr 8 `STup`

-- -----------------------------------------------------------------------------
-- CloTT
-- -----------------------------------------------------------------------------

-- |An FRP program of a type, executed in an environment
data CloTT :: CloTy -> * -> * where
  CloTT :: EvalRead a -> EvalState a -> P.Expr a -> Sing t -> CloTT t a

deriving instance Typeable a => Typeable (CloTT t a)

instance Show (CloTT t a) where
  show (CloTT er es expr sing) = pps expr

-- -- |Use template haskell to generate a singleton value that represents
-- -- an FRP type
typeToSingExp :: Type a Poly -> ExpQ
typeToSingExp (A _ typ') = case typ' of
  P.TFree (P.UName nm) -> 
    let nmQ = pure (S.LitT (S.StrTyLit nm))
    in  [| SFree (Proxy @($(nmQ))) |]
  t1 P.:->: t2         -> 
    let s1 = typeToSingExp t1
        s2 = typeToSingExp t2
    in  [| $(s1) `SArr` $(s2) |]
  t1 `P.TApp` t2          -> 
    let s1 = typeToSingExp t1
        s2 = typeToSingExp t2
    in  [| $(s1) `SApp` $(s2) |]
  P.TTuple ts -> 
    case ts of
      (x1 : x2 : xs) -> do
        let s1 = typeToSingExp x1
            s2 = typeToSingExp x2
            base = [| $(s1) `SPair` $(s2) |]
        foldr (\x acc -> [| STup $(typeToSingExp x) $(acc) |]) base xs -- foldl' here but its never gonna be a real problem
      _ -> fail $ "Cannot convert tuples of " ++ show (length ts) ++ " elements"

  _                    -> fail "Can only convert free types, tuples, and arrow types atm"

class ToHask (t :: CloTy) (r :: *) | t -> r where
  toHask :: Sing t -> Value a -> r

class ToCloTT (r :: *) (t :: CloTy) | t -> r where
  toCloTT :: Sing t -> r -> Value a

execute :: ToHask t r => CloTT t a -> r
execute (CloTT er st expr sing) = toHask sing $ runEvalMState (evalExprCorec expr) er st

transform :: (ToCloTT hask1 clott1, ToHask clott2 hask2)
          => CloTT (clott1 :->: clott2) a -> hask1 -> hask2
transform (CloTT er st expr (SArr s1 s2)) input = toHask s2 $ runEvalMState (evl expr) er st where
  evl e = do 
    Closure cenv nm e <- evalExprStep e
    let inv = toCloTT s1 input
    let cenv' = extendEnv nm inv cenv
    withEnv (combine cenv') $ evalExprCorec e


--   TyPrim _ TyNat  -> T.conE 'SNat
--   TyPrim _ TyBool -> T.conE 'SBool
--   TyPrim _ TyUnit -> T.conE 'SUnit
--   TyAlloc _       -> T.conE 'SAlloc
--   TySum _ t1 t2 ->
--     let e1 = typeToSingExp t1
--         e2 = typeToSingExp t2
--     in  T.conE 'SSum `T.appE` e1 `T.appE` e2
--   TyProd _ t1 t2    ->
--     let e1 = typeToSingExp t1
--         e2 = typeToSingExp t2
--     in  runQ [| SProd $(e1) $(e2) |]
--   TyArr _ t1 t2    ->
--     let e1 = typeToSingExp t1
--         e2 = typeToSingExp t2
--     in  runQ [| SArr $(e1) $(e2) |]
--   TyStream _ t ->
--     let e = typeToSingExp t
--     in  runQ [| SStream $(e) |]
--   TyStable _ t -> typeToSingExp t
--   TyLater  _ t -> typeToSingExp t
--   TyVar _ _    -> fail "FRP types must be fully instantiated when marshalled"
--   TyRec _ _ _  -> fail "Recursive types are not supported"

