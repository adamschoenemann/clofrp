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
import CloFRP.AST hiding (Fold, Constr, (:->:))
import qualified CloFRP.AST as P
import CloFRP.Annotated
import CloFRP.Eval.Value
import CloFRP.Eval
import Data.Proxy
import CloFRP.QuasiQuoter
import CloFRP.Pretty
import CloFRP.Examples

import Text.Parsec.Pos
import Data.Text (Text)
import NeatInterpolation
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

data Tree a = Leaf a | Br (Tree a) (Tree a) deriving (Eq, Show)

instance ToHask c h => ToHask (CTFree "Tree" :@: c) (Tree ()) where
  toHask (_ `SApp` s1) v = go v where
    go (Fold (Constr "Leaf" _)) = Leaf ()
    go (Fold (Constr "Br" (l : r : _))) = Br (go l) (go r)
  -- toHask s@(_ `SApp` s1) (Fold (Constr "Leaf" [x])) = Leaf (toHask s1 x)
  -- toHask s@(_ `SApp` s1) (Fold (Constr "Br" (l : r : _))) =
  --   Br (toHask s l) (toHask s r)
  -- toHask s v = undefined -- error $ "did not expect" ++ pps v

data BinTree a = Branch a (BinTree a) (BinTree a) | Done deriving (Eq, Show)

instance ToHask c h => ToHask (CTBinTree :@: c) (BinTree h) where
  toHask (_ `SApp` s1) v = go 10 v where
    go 0 _ = Done
    go n (Fold (Constr "Branch" (x : l : r : _))) = 
      Branch (toHask s1 x) (go (n-1) l) (go (n-1) r)
    go n v = error $ "did not expect " ++ pps v
  -- toHask s@(_ `SApp` _ `SApp` s1) (Fold (Constr "Branch" (x : l : r : _))) =
  --   Branch (toHask s1 x) (toHask s l) (toHask s r)
  -- toHask s v = error $ "did not expect" ++ pps v

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

replaceMin = 
  [clott|
      -- applicative structure        
      pure : forall (k : Clock) a. a -> |>k a.
      pure = \x -> \\(af : k) -> x.

      app : forall (k : Clock) a b. |>k (a -> b) -> |>k a -> |>k b.
      app = \lf la -> \\(af : k) -> 
        let f = lf [af] in
        let a = la [af] in
        f a.

      -- functor
      map : forall (k : Clock) a b. (a -> b) -> |>k a -> |>k b.
      map = \f la -> app (pure f) la.

      fst : forall a b. (a, b) -> a.
      fst = \x -> case x of | (y, z) -> y.

      snd : forall a b. (a, b) -> b.
      snd = \x -> case x of | (y, z) -> z.

      feedback : forall (k : Clock) (b : Clock -> *) u. (|>k u -> (b k, u)) -> b k.
      feedback = \f -> fst (fix (\x -> f (map snd x))).

      data NatF f = Z | S f deriving Functor.
      type Nat = Fix NatF.

      z : Nat.
      z = fold Z.

      s : Nat -> Nat.
      s = \x -> fold (S x).

      plus : Nat -> Nat -> Nat.
      plus = \m n -> 
        let body = \x ->
          case x of
            | Z -> n
            | S (m', r) -> fold (S r)
        in  primRec {NatF} body m.

      mult : Nat -> Nat -> Nat.
      mult = \m n ->
        let body = \x -> case x of
          | Z -> z
          | S (m', r) -> plus n r
        in primRec {NatF} body m.

      data TreeF a f = Leaf a | Br f f deriving Functor.
      type Tree a = Fix (TreeF a).

      min : Nat -> Nat -> Nat.
      min = primRec {NatF} (\m n -> 
        case m of 
        | Z -> fold Z
        | S (m', r) -> fold (S (r n))
      ).

      leaf : forall a. a -> Tree a.
      leaf = \x -> fold (Leaf x).

      br : forall a. Tree a -> Tree a -> Tree a.
      br = \l r -> fold (Br l r).

      data Delay a (k : Clock) = Delay (|>k a).

      replaceMinBody : forall (k : Clock). Tree Nat -> |>k Nat -> (Delay (Tree Nat) k, Nat).
      replaceMinBody = primRec {TreeF Nat} (\t m ->
        case t of
        | Leaf x -> (Delay (map leaf m), x)
        | Br (l, lrec) (r, rrec) -> 
          let (Delay l', ml) = lrec m {- : (Delay (Tree Nat) k, Nat) -} in
          let (Delay r', mr) = rrec m {- : (Delay (Tree Nat) k, Nat) -} in
          let m'       = min ml mr in
          (Delay (app (map br l') r'), m')
      ).

      replaceMinK : forall (k : Clock). Tree Nat -> Delay (Tree Nat) k.
      replaceMinK = \t -> feedback (replaceMinBody t).

      replaceMin : Tree Nat -> Tree Nat.
      replaceMin = \t -> 
        let Delay t' = replaceMinK {K0} t
        in t' [<>].
      
      ofHeight : Nat -> Tree Nat.
      ofHeight = \nat -> 
        fst (primRec {NatF} (\m n ->
          case m of  
            | Z -> (leaf z, s n)
            | S (m', r) -> 
              let (t1, n1) = r n in
              let (t2, n2) = r n1
              in  (br t1 t2, n2)
        ) nat z).
      
      main : Tree Nat.
      main = 
        let five = s (s (s (s (s z))))
        in  replaceMin (ofHeight (plus (s (s (s (s z)))) five)).
    |]

ofHeight :: Int -> Tree Int
ofHeight !n
  | n <= 0 = Leaf n
  | otherwise = Br (ofHeight (n-1)) (ofHeight (n-1))

replaceMinHask :: Tree Int -> Tree Int
replaceMinHask t = let (t', m) = replaceMinBody t m in t' where
  replaceMinBody (Leaf x) m = (Leaf m, x)
  replaceMinBody (Br l r) m =
    let (l', ml) = replaceMinBody l m
        (r', mr) = replaceMinBody r m
    in (Br l' r', min ml mr)

-- streamProcessing = 
--   [clott|
--     data SPF i o (k : Clock) f
--       = Get (i -> f)
--       | Put o (|>k f)
--       deriving Functor.
    
--     type SP i o (k : Clock) = Fix (SPF i o k).

--     step : forall (k : Clock) i o. SP i o k -> SPF i o k (Fix (SPF i o k)).
--     step = unfold.

--     data StreamF (k : Clock) a f = Cons a (|>k f).
--     type Stream (k : Clock) a = Fix (StreamF k a).
--     data CoStream a = Cos (forall (k : Clock). Stream k a).

--     hd : forall a. CoStream a -> a.
--     hd = \xs -> 
--       let Cos s = xs
--       in case unfold s of
--           | Cons x xs' -> x.

--     -- see if you can do this better with let generalization
--     tl : forall a. CoStream a -> CoStream a.
--     tl = \x ->
--       let Cos s = x in
--       let r = (case unfold s of
--               | Cons x xs' -> xs' 
--               ) : forall (k : Clock). |>k (Stream k a)
--       in Cos (r [<>]).

--     fst : forall a b. (a, b) -> a.
--     fst = \x -> case x of | (y, z) -> y.

--     snd : forall a b. (a, b) -> b.
--     snd = \x -> case x of | (y, z) -> z.

--     -- applicative structure        
--     pure : forall (k : Clock) a. a -> |>k a.
--     pure = \x -> \\(af : k) -> x.

--     app : forall (k : Clock) a b. |>k (a -> b) -> |>k a -> |>k b.
--     app = \lf la -> \\(af : k) -> 
--       let f = lf [af] in
--       let a = la [af] in
--       f a.

--     -- functor
--     map : forall (k : Clock) a b. (a -> b) -> |>k a -> |>k b.
--     map = \f la -> app (pure f) la.

--     -- fixpoint above with full types
--     applyfix : forall (k : Clock) i o. |>k (SP i o k -> CoStream i -> CoStream o) -> SP i o k -> CoStream i -> CoStream o.
--     applyfix = \rec -> 
--       primRec {SPF i o k} (\x s ->
--         case x of
--         | Get f -> let (sp', g) = f (hd s) in g (tl s)
--         | Put b sp -> 
--           let sp1 = map fst sp in
--           cos b (app (app rec sp1) (pure s))
--       ).

--     -- it even works without annotations!
--     apply : forall (k : Clock) i o. SP i o k -> CoStream i -> CoStream o.
--     apply = fix (\rec -> 
--       primRec {SPF i o k} (\x s ->
--         case x of
--         | Get f -> (snd (f (hd s))) (tl s) 
--         | Put b sp -> 
--           let sp1 = map fst sp in
--           cos b (app (app rec sp1) (pure s))
--       )).

--     cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
--     cos = \x xs -> 
--       Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). 

--     uncos : forall (k : Clock) a. CoStream a -> Stream k a.
--     uncos = \xs -> case xs of | Cos xs' -> xs'.

--     spid : forall i. SP i i K0.
--     spid = fix (\f -> fold (Get (\i -> fold (Put i f)))).

--     const : forall (k : Clock) a. a -> Stream k a.
--     const = \x -> fix (\f -> fold (Cons x f)).

--     data Unit = MkUnit.

--     main : Stream K0 Unit.
--     main = uncos (apply spid (Cos (const MkUnit))).
--   |]

-- main = defaultMain [bench "const" (whnf const ())]
main :: IO ()
main = do
  putStrLn "running benchmark"
  bench_binTree
  -- bench_replaceMin
  -- let n = 500000
  -- let truefalse = (True : False : truefalse :: [Bool])
  -- let trues = repeat True
  -- putStrLn . show $ take 100000 (transform everyOtherTrans truefalse)
  -- putStrLn . show $ take n (streamTrans simpleTrans trues)
  -- putStrLn . show $ take 8000000 (execute everyOtherExec)

truefalse :: [Bool]
truefalse = True : False : truefalse 

coStreamTrans :: (Pretty a, ToCloFRP hask1 clott1, ToHask clott2 hask2)
              => CloFRP ('CTFree "CoStream" ':@: clott1
                        ':->:
                        'CTFree "Stream" ':@: 'CTFree "K0" ':@: clott2) a
              -> [hask1] -> [hask2]
coStreamTrans (CloFRP er st expr ((s1 `SApp` s2) `SArr` (s3 `SApp` s4 `SApp` s5))) input = 
  fromCloFRPStream $ runEvalMState (begin input) er st
  where
    begin xs = do
      Closure env nm e@(A ann _) <- evalExprStep expr
      let e' = P.substExpr (A ann (P.Var "Cos") `App` A ann (P.Prim P.Input)) nm e
      let inputs = map (makeInput ann) xs
      withEnv (const env) $ evalExprOver inputs e'

    makeInput ann z = Fold $ Constr "Cons" [toCloFRP s2 z, TickClosure mempty "#_" $ A ann $ P.Prim P.Input]

    fromCloFRPStream (Fold (Constr "Cons" [v, c])) = toHask s5 v : fromCloFRPStream c
    fromCloFRPStream v = error $ "fromCloFRPStream:" ++ pps v

bench_everyOtherTrans :: IO ()
bench_everyOtherTrans =
  putStrLn . show $ take 100000 (coStreamTrans everyOtherTrans truefalse)

bench_everyOtherExec :: IO ()
bench_everyOtherExec =
  putStrLn . show $ take 100000 (execute everyOtherExec)

bench_replaceMin :: IO ()
bench_replaceMin = 
  putStrLn . show $ replaceMinHask (ofHeight 9)
  -- putStrLn . show $ execute replaceMin

bench_binTree :: IO ()
bench_binTree = do
  let n = 10
  putStrLn . show $ runCloFRP binTree
  where
    takeBinTreeVal 0 _ = Done
    takeBinTreeVal !n (Fold (Constr "Branch" (x : l : r : _))) =
      Branch () (takeBinTreeVal (n-1) l) (takeBinTreeVal (n-1) l)
    takeBinTreeVal !n _ = Done

bench_clott_add :: IO ()
bench_clott_add = do
  let n = 200000
  let inputs = zip (repeat 1) (repeat 1)
  let output = take n (streamTrans clott_add inputs)
  putStrLn . show $ output
