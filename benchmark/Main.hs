{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

-- You can benchmark your code quickly and effectively with Criterion. See its
-- website for help: <http://www.serpentine.com/criterion/>.
import Criterion.Main

import CloFRP.Interop
import CloFRP.AST hiding (Fold, Constr)
import CloFRP.Eval.Value
import CloFRP.Eval
import Data.Proxy
import CloFRP.QuasiQuoter
import CloFRP.Pretty
import CloFRP.Examples

import Text.Parsec.Pos
import Data.String (fromString)

instance Pretty SourcePos where
  pretty = fromString . show

instance ToCloFRP Bool ('CTFree "Bool") where
  toCloFRP (SFree px) True  = (Constr "True" [])  
  toCloFRP (SFree px) False = (Constr "False" []) 

instance ToHask ('CTFree "Bool") Bool where
  toHask (SFree px) (Constr "True" [])  = True
  toHask (SFree px) (Constr "False" []) = False
  toHask (SFree px) v                   = error ("Expected Constr but got " ++ pps (takeConstr 2 v))

instance ToHask ('CTFree "Nat") Int where
  toHask (SFree px) (Fold (Constr "Z" []))  = 0
  toHask (SFree px) (Fold (Constr "S" [r])) = succ (toHask (SFree px) r)
  toHask (SFree px) _                = undefined

instance ToCloFRP Int ('CTFree "Nat") where
  toCloFRP (SFree px) 0 = Fold (Constr "Z" [])
  toCloFRP (SFree px) n = Fold (Constr "S" [toCloFRP (SFree px) (n-1)])

instance ToHask t r => ToHask ('CTFree "Stream" :@: u :@: t) [r] where
  toHask s@((s1 `SApp` s2) `SApp` s3) (Fold (Constr "Cons" [v, c])) = toHask s3 v : toHask s c
  toHask s@((s1 `SApp` s2) `SApp` s3) v = error ("Expected fold (Cons x ..) but got " ++ pps (takeConstr 2 v))

-- haskell lists to clott streams over k₀
instance ToCloFRP hask clott => ToCloFRP [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) where
  toCloFRP s@(s1 `SApp` s2) xs = clottStream s2 xs

-- clottStream s2 (x : xs') = Fold (Constr "Cons" [toCloFRP s2 x, clottStream s2 xs'])
clottStream s2 (x : xs') = Fold (Constr "Cons" [toCloFRP s2 x, Delay (clottStream s2 xs')])
clottStream s2 []        = runtimeErr "End of stream"

-- haskell lists to clott coinductive streams 
instance ToCloFRP [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) => ToCloFRP [hask] ('CTFree "CoStream" :@: clott) where
  toCloFRP s@(s1 `SApp` s2) xs = 
    let strsing = SFree (Proxy @"Stream") `SApp` SFree (Proxy @"K0") `SApp` s2
    in  Constr "Cos" [toCloFRP strsing xs] where

type CTStream = 'CTFree "Stream" :@: 'CTFree "K0"
type CTBinTree = 'CTFree "BinTree" :@: 'CTFree "K0"

instance ToHask ('CTFree "Unit") () where
  toHask _ (Constr "MkUnit" []) = ()

instance ToHask c h => ToHask (CTBinTree :@: c) (BinTree h) where
  toHask s@(_ `SApp` _ `SApp` s1) (Fold (Constr "Branch" (x : l : r : _))) =
    Branch (toHask s1 x) (toHask s l) (toHask s r)
  toHask s v = undefined -- error $ "did not expect" ++ pps v

data BinTree a = Branch a (BinTree a) (BinTree a) | Done deriving (Eq, Show)

takeBinTree :: Int -> BinTree a -> BinTree a
takeBinTree n t 
  | n <= 0 = Done
  | otherwise = case t of
      Done -> Done
      Branch x l r -> Branch x (takeBinTree (n-1) l) (takeBinTree (n-1) r)

constTree :: a -> BinTree a
constTree x = Branch x (constTree x) (constTree x)

-- instance Show a => Show (BinTree a) where
--   showsPrec p (Done) = shows "Done"
--   showsPrec p (Branch x l r) = ("Branch " ++) . (show x ++) . showsPrec p l . showsPrec p r

-- type CTNat = 'CTFree "Nat"

everyOtherExec = [clott|
  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).
  data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

  cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
  cos = \x xs -> 
    Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

  uncos : forall (k : Clock) a. CoStream a -> Stream k a.
  uncos = \xs -> case xs of | Cos xs' -> xs'.

  cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
  cons = \x xs -> fold (Cons x xs).

  hdk : forall (k : Clock) a. Stream k a -> a.
  hdk = \xs ->
    case unfold xs of
    | Cons x xs' -> x.

  tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
  tlk = \xs ->
    case unfold xs of
    | Cons x xs' -> xs'.

  hd : forall a. CoStream a -> a.
  hd = \xs -> hdk {K0} (uncos xs).
  
  tl : forall a. CoStream a -> CoStream a.
  tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

  eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
  eof = \f xs -> 
    let tl2 = tl (tl xs) in
    let dtl = (\\(af : k) -> (f [af]) tl2) in
    cos (hd xs) dtl.

  eo : forall a. CoStream a -> CoStream a.
  eo = fix eof.

  data Bool = True | False.        
  truefalse : forall (k : Clock). Stream k Bool.
  truefalse = fix (\g -> cons True (\\(af : k) -> cons False g)).

  main : Stream K0 Bool.
  main = 
    let Cos xs = eo (Cos truefalse) in
    xs.
|]

everyOtherTrans = [clott|
  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).
  data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

  cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
  cos = \x xs -> 
    Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

  uncos : forall (k : Clock) a. CoStream a -> Stream k a.
  uncos = \xs -> case xs of | Cos xs' -> xs'.

  cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
  cons = \x xs -> fold (Cons x xs).

  hdk : forall (k : Clock) a. Stream k a -> a.
  hdk = \xs ->
    case unfold xs of
    | Cons x xs' -> x.

  tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
  tlk = \xs ->
    case unfold xs of
    | Cons x xs' -> xs'.

  hd : forall a. CoStream a -> a.
  hd = \xs -> hdk {K0} (uncos xs).
  
  tl : forall a. CoStream a -> CoStream a.
  tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

  eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
  eof = \f xs -> 
    let tl2 = tl (tl xs) in
    let dtl = (\\(af : k) -> (f [af]) tl2) in
    cos (hd xs) dtl.

  eo : forall a. CoStream a -> CoStream a.
  eo = fix eof.

  data Bool = True | False.

  main : CoStream Bool -> Stream K0 Bool.
  main = \input ->
    let Cos xs = eo input in
    xs.
|]

simpleTrans = [clott|
  data StreamF (k : Clock) a f = Cons a (|>k f) deriving Functor.
  type Stream (k : Clock) a = Fix (StreamF k a).
  data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).
  data Bool = True | False.        

  uncos : forall (k : Clock) a. CoStream a -> Stream k a.
  uncos = \xs -> case xs of | Cos xs' -> xs'.

  tlk : forall (k : Clock) a. Stream k a -> |>k (Stream k a).
  tlk = \xs ->
    case unfold xs of
    | Cons x xs' -> xs'.

  tl : forall a. CoStream a -> CoStream a.
  tl = \xs -> Cos ((tlk (uncos xs)) [<>]).

  negate : forall (k : Clock). Stream k Bool -> Stream k Bool.
  negate = fix (\g xs ->
     case unfold xs of 
     | Cons x xs'-> 
       let x' = (case x of | True -> False | False -> True) : Bool
       in  fold (Cons x' (\\(af : k) -> (g [af]) (xs' [af])))
  ).

  fixid : forall (k : Clock) a. Stream k a -> Stream k a.
  fixid = fix (\g xs -> 
    case unfold xs of
    | Cons x xs' -> fold (Cons x (\\(af : k) -> g [af] (xs' [af])))
  ).

  main : Stream K0 Bool -> Stream K0 Bool.
  main = \xs -> negate xs.
|]

binTree = [clott|
  data BinTreeF (k : Clock) a f = Branch a (|>k f) (|>k f).
  type BinTree (k : Clock) a = Fix (BinTreeF k a).
  data Unit = MkUnit.
  data Bool = True | False.

  data StreamF (k : Clock) a f = Cons a (|>k f).
  type Stream (k : Clock) a = Fix (StreamF k a).

  constBinTree : forall (k : Clock) a. a -> BinTree k a.
  constBinTree = \x ->
    fix (\g -> fold (Branch x g g)).

  -- repeat : forall (k : Clock) a. a -> Stream k a.
  -- repeat = \x -> fix (\g -> fold (Cons x g)).

  main : BinTree K0 Unit.
  main = constBinTree MkUnit.

  -- main : Stream K0 Bool.
  -- main = repeat True.
|]

-- main = defaultMain [bench "const" (whnf const ())]
main :: IO ()
main = bench_binTree
  -- let n = 500000
  -- let truefalse = (True : False : truefalse :: [Bool])
  -- let trues = repeat True
  -- putStrLn . show $ take 100000 (transform everyOtherTrans truefalse)
  -- putStrLn . show $ take n (streamTrans simpleTrans trues)
  -- putStrLn . show $ take 8000000 (execute everyOtherExec)

bench_binTree :: IO ()
bench_binTree = do
  let n = 20
  putStrLn . show $ takeBinTree n $ execute binTree

bench_clott_add :: IO ()
bench_clott_add = do
  let n = 200000
  let inputs = zip (repeat 1) (repeat 1)
  let output = take n (streamTrans clott_add inputs)
  putStrLn . show $ output
