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

-- You can benchmark your code quickly and effectively with Criterion. See its
-- website for help: <http://www.serpentine.com/criterion/>.
import Criterion.Main

import CloTT.Interop
import CloTT.AST hiding (Fold, Constr)
import CloTT.Eval.Value
import CloTT.Eval
import Data.Proxy
import CloTT.QuasiQuoter
import CloTT.Pretty

instance ToCloTT Bool ('CTFree "Bool") where
  toCloTT (SFree px) True  = (Constr "True" [])  
  toCloTT (SFree px) False = (Constr "False" []) 

instance ToHask ('CTFree "Bool") Bool where
  toHask (SFree px) (Constr "True" [])  = True
  toHask (SFree px) (Constr "False" []) = False
  toHask (SFree px) v                   = error ("Expected Constr but got " ++ pps (takeConstr 2 v))

instance ToHask t r => ToHask ('CTFree "Stream" :@: u :@: t) [r] where
  toHask s@((s1 `SApp` s2) `SApp` s3) (Fold (Constr "Cons" [v, c])) = toHask s3 v : toHask s c
  toHask s@((s1 `SApp` s2) `SApp` s3) v = error ("Expected fold (Cons x ..) but got " ++ pps (takeConstr 2 v))

-- haskell lists to clott streams over k₀
instance ToCloTT hask clott => ToCloTT [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) where
  toCloTT s@(s1 `SApp` s2) xs = clottStream s2 xs

-- clottStream s2 (x : xs') = Fold (Constr "Cons" [toCloTT s2 x, clottStream s2 xs'])
clottStream s2 (x : xs') = Fold (Constr "Cons" [toCloTT s2 x, clottStream s2 xs'])
clottStream s2 []        = runtimeErr "End of stream"

-- haskell lists to clott coinductive streams 
instance ToCloTT [hask] ('CTFree "Stream" :@: 'CTFree "K0" :@: clott) => ToCloTT [hask] ('CTFree "CoStream" :@: clott) where
  toCloTT s@(s1 `SApp` s2) xs = 
    let strsing = SFree (Proxy @"Stream") `SApp` SFree (Proxy @"K0") `SApp` s2
    in  Constr "Cos" [toCloTT strsing xs] where

type CTStream = 'CTFree "Stream" :@: 'CTFree "K0"
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

  main : CoStream Bool -> Stream K0 Bool.
  main = \input ->
    let Cos xs = input in negate xs.
|]
-- main = defaultMain [bench "const" (whnf const ())]
main :: IO ()
main = do
  let n = 100000
  let truefalse = (True : False : truefalse :: [Bool])
  let trues = repeat True
  -- putStrLn . show $ take 100000 (transform everyOtherTrans truefalse)
  putStrLn . show $ take n (transform simpleTrans trues)
  -- putStrLn . show $ take 8000000 (execute everyOtherExec)
