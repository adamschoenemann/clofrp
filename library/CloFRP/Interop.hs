
{-|
Module      : CloFRP.Interop
Description : Reflecting CloFRP-Types into the Haskell type-system
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module CloFRP.Interop where

import GHC.TypeLits
import           Language.Haskell.TH ( Exp (..), ExpQ, Lit (..), Pat (..), Q
                                     , DecQ, mkName, runQ)
import qualified Language.Haskell.TH.Syntax as S
import qualified Language.Haskell.TH as T
import           Data.Data
import           Debug.Trace

import qualified CloFRP.AST as P
import           CloFRP.AST (PolyType, TySort(..))
import           CloFRP.Annotated
import           CloFRP.AST.Helpers
import           CloFRP.Eval
import           CloFRP.Pretty

-- -----------------------------------------------------------------------------
-- CloTy
-- -----------------------------------------------------------------------------

infixr 0 :->:
infixl 9 :@:

-- | The type of CloFRP-types that can be reflected
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
  SFree   :: KnownSymbol s => Proxy s -> Sing ('CTFree s)
  SPair   :: Sing t1 -> Sing t2            -> Sing ('CTTuple '[t1, t2])
  STup    :: Sing t  -> Sing ('CTTuple ts) -> Sing ('CTTuple (t ': ts))
  SApp    :: Sing t1 -> Sing t2            -> Sing (t1 ':@:  t2)
  SArr    :: Sing t1 -> Sing t2            -> Sing (t1 ':->: t2)

instance Show (Sing ct) where
  show sng = case sng of
    SFree px -> symbolVal px
    t1 `SArr` t2 -> show t1 ++ " -> " ++ show t2
    t1 `SApp` t2 -> "(" ++ show t1 ++ " " ++ show t2 ++ ")"
    t1 `SPair` t2 -> "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
    STup t ts ->
      "(" ++ show t ++ ", " ++ tupShow ts
      where
        tupShow :: Sing ('CTTuple ts') -> String
        tupShow (SPair x y) = show x ++ ", " ++ show y ++ ")"
        tupShow (STup t' ts') = show t' ++ ", " ++ tupShow ts'



deriving instance Eq (Sing a)
-- deriving instance Show (Sing a)
deriving instance Typeable (Sing a)

-- |Reify a singleton back into an CloFRP type. Not used presently
reifySing :: Sing t -> PolyType ()
reifySing = \case
  SFree px -> A () $ P.TFree (P.UName $ symbolVal px)
  t1 `SArr` t2 -> A () $ reifySing t1 P.:->: reifySing t2
  t1 `SApp` t2 -> A () $ reifySing t1 `P.TApp`  reifySing t2
  t1 `SPair` t2 -> A () $ P.TTuple [reifySing t1, reifySing t2]
  STup t ts ->
    A () $ P.TTuple (reifySing t : tupleSing ts)
    where
        tupleSing :: Sing (CTTuple ts') -> [PolyType ()]
        tupleSing (SPair x y) = [reifySing x, reifySing y]
        tupleSing (STup t' ts') = reifySing t' : tupleSing ts'

infixr 0 `SArr`
infixl 9 `SApp`
infixr 8 `STup`

-- -----------------------------------------------------------------------------
-- CloFRP
-- -----------------------------------------------------------------------------

-- |An FRP program of a type, executed in an environment
data CloFRP :: CloTy -> * -> * where
  CloFRP :: EvalRead a -> EvalState a -> P.Expr a -> Sing t -> CloFRP t a

deriving instance Typeable a => Typeable (CloFRP t a)

instance Show (CloFRP t a) where
  show (CloFRP er es expr sing) = pps expr

-- |Use template haskell to generate a singleton value that represents
-- a CloFRP type
typeToSingExp :: PolyType a -> ExpQ
typeToSingExp (A _ typ') = case typ' of
  P.TFree (P.UName nm) ->
    let nmQ = pure (S.LitT (S.StrTyLit nm))
    in  [| SFree (Proxy :: (Proxy $(nmQ))) |]
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
        foldr (\x acc -> [| STup $(typeToSingExp x) $(acc) |]) base xs 
      _ -> fail $ "Cannot convert tuples of " ++ show (length ts) ++ " elements"

  _                    -> fail "Can only convert free types, tuples, and arrow types atm"

class ToHask (t :: CloTy) (r :: *) | t -> r where
  toHask :: Sing t -> Value a -> r

class ToCloFRP (r :: *) (t :: CloTy) | t -> r where
  toCloFRP :: Sing t -> r -> Value a

instance ToHask ('CTFree "Int") Integer where
  toHask _ (Prim (IntVal i)) = i
  toHask _ v = error $ "expected int but got " ++ pps v

instance ToCloFRP Integer ('CTFree "Int") where
  toCloFRP _ i = Prim (IntVal i)

instance (ToCloFRP h1 c1, ToCloFRP h2 c2) => ToCloFRP (h1, h2) ('CTTuple [c1, c2]) where
  toCloFRP (SPair s1 s2) (x1, x2) = Tuple [toCloFRP s1 x1, toCloFRP s2 x2]
  toCloFRP (STup ss s)   (x1, x2) = error "impossible" -- Tuple [toCloFRP s1 x1, toCloFRP s2 x2]

instance (ToHask c1 h1, ToHask c2 h2) => ToHask ('CTTuple [c1, c2]) (h1, h2) where
  toHask (SPair s1 s2) (Tuple [x1, x2]) = (toHask s1 x1, toHask s2 x2)
  toHask _ v = error $ show $ "Expected tuple but got" <+> pretty v

-- cant make this inductive, since tuples are not inductive in haskell.
-- alternatively, one could marshall to HList instead which would allow it
instance (ToHask c1 h1, ToHask c2 h2, ToHask c3 h3) => ToHask ('CTTuple '[c1,c2,c3]) (h1,h2,h3) where
  toHask (s1 `STup` (s2 `SPair` s3)) (Tuple [x1,x2,x3]) = (toHask s1 x1, toHask s2 x2, toHask s3 x3)
  toHask _ v = error $ show $ "Expected tuple but got" <+> pretty v

execute :: (Pretty a, ToHask t r) => CloFRP t a -> r
execute (CloFRP er st expr sing) = toHask sing $ runEvalMState (evalExprCorec expr) er st

runCloFRP :: (Pretty a) => CloFRP t a -> Value a
runCloFRP (CloFRP er st expr sing) = runEvalMState (evalExprCorec expr) er st

stepCloFRP :: (Pretty a) => CloFRP t a -> Value a
stepCloFRP (CloFRP er st expr sing) = runEvalMState (evalExprStep expr) er st

transform :: (Pretty a, ToCloFRP hask1 clott1, ToHask clott2 hask2)
          => CloFRP (clott1 :->: clott2) a -> hask1 -> hask2
transform (CloFRP er st expr (SArr s1 s2)) input = toHask s2 $ runEvalMState (evl expr) er st where
  evl e = do
    Closure cenv nm ne <- evalExprStep e
    let inv = toCloFRP s1 input
    let cenv' = extendEnv nm inv cenv
    withEnv (combine cenv') $ evalExprCorec ne

-- TODO: Generalizing these things is not easy
evalExprOver :: forall a. Pretty a  => [(Value a)] -> P.Expr a -> EvalM a (Value a)
evalExprOver f = foldr mapping (const $ pure $ runtimeErr "End of input") f where
  mapping :: Value a -> (P.Expr a -> EvalM a (Value a)) -> (P.Expr a -> EvalM a (Value a))
  mapping x accfn expr = do
    v <- withInput x $ evalExprStep expr
    case v of
      Fold (Constr "Cons" [y, TickClosure cenv nm e]) -> do
        cont <- withEnv (const $ extendEnv nm (Prim Tick) cenv) $ accfn e
        pure $ Fold $ Constr "Cons" [y, cont]
      _ -> error (pps v)


streamTrans :: (Pretty a, ToCloFRP hask1 clott1, ToHask clott2 hask2, KnownSymbol k)
            => CloFRP ('CTFree "Stream" ':@: 'CTFree k ':@: clott1
                      ':->:
                      'CTFree "Stream" ':@: 'CTFree k ':@: clott2) a
            -> [hask1] -> [hask2]
streamTrans (CloFRP er st expr ((s1 `SApp` _ `SApp` s2) `SArr` (s3 `SApp` s4 `SApp` s5))) input = do
  fromCloFRPStream $ runEvalMState (begin input) er st
  where
    begin xs = do
      Closure env nm e@(A ann _) <- evalExprStep expr
      let e' = P.substExpr (P.Prim P.Input) nm e
      let inputs = map (makeInput ann) xs
      withEnv (const env) $ evalExprOver inputs e'

    makeInput ann z = Fold $ Constr "Cons" [toCloFRP s2 z, TickClosure mempty "_" $ A ann $ P.Prim P.Input]

    fromCloFRPStream (Fold (Constr "Cons" [v, c])) = toHask s5 v : fromCloFRPStream c
    fromCloFRPStream v = error $ "fromCloFRPStream:" ++ pps v