{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}

module CloTT.EvalSpec where

import Test.Tasty.Hspec
import Data.Either (isLeft)
import Data.String (fromString)
import NeatInterpolation
import Debug.Trace

import qualified CloTT.AST  as E
import qualified CloTT.AST.Prim    as P
import           CloTT.AST ((@->:), (@@:), Kind(..))
import           CloTT.AST (LamCalc(..))
import qualified Fixtures

import qualified Data.Map.Strict as M
import           CloTT.QuasiQuoter
import           CloTT.TestUtils
import           CloTT.Pretty
import           CloTT.Eval
import           CloTT.Annotated (unann, Annotated(..))

evalSpec :: Spec
evalSpec = do
  let eval0 e = runEvalM (evalExprStep e) mempty
  let eval environ e = runEvalM (evalExprStep e) (mempty { erEnv = environ })
  let int = Prim . IntVal
  let constr nm vs = Constr nm vs
  let c nm = (nm, Constr nm [])
  let (|->) = \x y -> (x,y) 
  let [s,z,cons,nil,just,nothing] = [c "S", c "Z", c "Cons", c "Nil", c "Just", c "Nothing"] :: [(E.Name, Value ())]


  describe "evalExprStep" $ do
    it "evals lambdas" $ do
      eval0 ("x" @-> "x") `shouldBe` (Closure [] "x" (E.var "x"))
    it "evals applications" $ do
      eval0 (("x" @-> "x") @@ E.int 10) `shouldBe` (int 10)
      let m = ["x" |-> int 10]
      eval0 (("x" @-> "y" @-> "x") @@ E.int 10) `shouldBe` (Closure m "y" (E.var "x"))
    it "evals tuples" $ do
      eval0 (("x" @-> E.tup ["x", E.int 10]) @@ E.int 9) `shouldBe` (Tuple [int 9, int 10])

    it "evals contructors (1)" $ do
      let m = [s, z]
      eval m ("S" @@ "Z") `shouldBe` (constr "S" [constr "Z" []])
    it "evals contructors (2)" $ do
      let m = [s,z,nil,cons]
      let explist = foldr (\x acc -> "Cons" @@ x @@ acc) "Nil"
      let vallist = foldr (\x acc -> constr "Cons" [x, acc]) (constr "Nil" [])
      eval m (explist $ map E.int [1..5]) `shouldBe` (vallist $ map int [1..5])
    it "evals contructors (3)" $ do
      let m = [s,z,just,nothing]
      let p = unann [unsafeExpr|
        S (S (S Z))
      |]
      let s' arg = Constr "S" [arg]
      eval m p `shouldBe` (s' $ s' $ s' (Constr "Z" []))
    it "evals contructors (4)" $ do
      let m = [s,z,just,nothing]
      let p = unann [unsafeExpr|
        let s = S in
        let z = Z in
        s (s (s z))
      |]
      let s' arg = Constr "S" [arg]
      eval m p `shouldBe` (s' $ s' $ s' (Constr "Z" []))
    -- it "evals contructors (3)" $ do
    --   let m = env [s,z,just,nothing]
    --   let p = unann [unsafeExpr
    --     let map = \f x -> case x of | Nothing -> Nothing | Just x' -> Just (f x') in
    --   |]
    --   eval m () `shouldBe` (vallist $ map int [1..5])

    it "evals let bindings (1)" $ do
      eval0 (unann [unsafeExpr| let x = 10 in let id = \y -> y in id x |]) `shouldBe` (int 10)
    it "evals let bindings (2)" $ do
      eval0 (unann [unsafeExpr| let x = 9 in let id = \x -> x in (id x, id id 10, id id id 11) |]) `shouldBe` (Tuple [int 9, int 10, int 11])
    it "evals let bindings (3)" $ do
      let m = [c "Wrap"]
      eval m (unann [unsafeExpr| (\x -> let Wrap x' = x in x') (Wrap 10) |]) `shouldBe` (int 10)

    describe "case expression evaluation" $ do
      let p1 e = unann [unsafeExpr|
        (\x -> case x of
          | Nothing -> 0
          | Just x -> x
        )
      |] @@ e
      let m = [s,z,just,nothing,cons,nil]
      it "evals case expressions (1)" $ do
        eval m (p1 ("Just" @@ E.int 10)) `shouldBe` (int 10)
      it "evals case expressions (2)" $ do
        eval m (p1 "Nothing") `shouldBe` (int 0)

      let p2 e = unann [unsafeExpr|
        (\x -> case x of
          | Nothing -> 0
          | Just Nil -> 1
          | Just (Cons x' xs') -> x'
        ) 
      |] @@ e
      it "evals case expressions (3)" $ do
        eval m (p2 ("Just" @@ ("Cons" @@ E.int 10 @@ "Nil"))) `shouldBe` (int 10)
      it "evals case expressions (4)" $ do
        eval m (p2 ("Just" @@ "Nil")) `shouldBe` (int 1)

      let p3 e = unann [unsafeExpr|
        \x -> case x of
          | z -> 10
          | (x, y) -> x
      |] @@ e

      it "evals case expressions (5)" $ do
        eval m (p3 (E.tup [E.int 1, E.int 2])) `shouldBe` (int 10)
    
    describe "fixpoints" $ do
      it "evals first iter of const stream correctly" $ do
        {-
          -- fix body => body (\\af -> fix body)

          fix body => 
          body (\\af -> body) =>
          (\xs -> fold (Cons x xs)) (\\af -> fix body) =>
          fold (Cons x (\\af -> fix body)) =>
          Cons x (\\af -> fix body) =>
          Cons x (body (\\af -> fix body)) =>
          Cons x (Cons x (\\af -> fix body))
        -}
        let p = unann [unsafeExpr|
          (\x -> let body = \xs -> fold (Cons x xs)
                 in  fix body
          ) 1
        |]
        let m = [cons]
        case eval m p of 
          (Constr "Cons" [Prim (IntVal 1), TickClosure _ (E.DeBruijn 0) b]) -> 
            b `shouldBe` (E.fixp @@ "body")
          e  -> failure ("did not expect " ++ show (pretty e))

      it "evals first iter of strmap correctly" $ do
        {-
          map S (const Z) =>
          fix mapfix (const Z) =>
          mapfix (\\af -> fix mapfix) (const Z) =>
          cons (S Z) (\\af -> mapfix [af] (xs' [af])) =>
          fold (Cons (S Z) (\\af -> mapfix [af] (xs' [af]))) =>
          Cons (S Z) (\\af -> mapfix [af] (xs' [af])) =>
        -}
        let p = unann [unsafeExpr|
          let cons = \x xs -> fold (Cons x xs) in 
          let strmap = \f -> 
            let mapfix = \g xs ->
                case unfold xs of
                | Cons x xs' -> 
                  let ys = \\(af : k) -> g [af] (xs' [af])
                  in  cons (f x) ys 
            in fix mapfix in
          let const = \x ->
             let body = \xs -> Cons x xs
             in  fix body
          in strmap S (const Z)
        |]
        let m = [s,z,cons]
        case eval m p of 
          (Constr "Cons" [Constr "S" [Constr "Z" []], TickClosure _ _ e]) ->
            e `shouldBe` "g" @@ "[af]" @@ ("xs'" @@ "[af]")
          e  -> failure ("did not expect " ++ show (pretty e))
    
  describe "evalExprCorec" $ do
    let evcorec environ x = 
          runEvalM (evalExprCorec x) (mempty { erEnv = environ })

    let evcorec0 x = evcorec mempty x
    it "forever terminates with primitives" $ do
      evcorec0 (E.int 10) `shouldBe` (int 10)
      evcorec [just] ("Just" @@ E.int 10) `shouldBe` (Constr "Just" [int 10])

    it "forever terminates with 2-step comp" $ do
      let e = "Cons" @@ E.int 1 @@ (("af", "k") `E.tAbs` ("Cons" @@ E.int 2 @@ "Nil"))
      evcorec [cons, nil] e `shouldBe` (Constr "Cons" [int 1, Constr "Cons" [int 2, Constr "Nil" []]])
    
    it "evals the constant stream" $ do
      let Right p = pexprua [text|
        let const = \x ->
            let body = \xs -> fold (Cons x xs)
            in  fix body
        in const Z
      |]
      let m = [s,z,cons]

      let cs = evcorec m p
      takeValueList vnatToInt 10 cs `shouldBe` (replicate 10 0)

    it "evals the stream of naturals" $ do
      let Right p = pexprua [text|
        let cons = \x xs -> fold (Cons x xs) in 
        let strmap = \f -> 
          let mapfix = \g xs ->
              case unfold xs of
              | Cons x xs' -> 
                let ys = \\(af : k) -> g [af] (xs' [af])
                in  cons (f x) ys 
          in fix mapfix in
        let z = fold Z in
        let s = \x -> fold (S x) in
        let nats = fix (\g -> cons z (\\(af : k) -> (strmap s) (g [af]))) in
        nats
      |]
      let m = [s,z,cons]
      let cs = evcorec m p
      takeValueList vnatToInt 10 cs `shouldBe` ([0..9])
    
  describe "evalProg" $ do
    it "works for stream of naturals" $ do
      let Right p = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).
        data NatF f = Z | S f.
        type Nat = Fix NatF.

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

        strmap : forall (k : Clock) a b. (a -> b) -> Stream k a -> Stream k b.
        strmap = \f -> 
          --  mapfix : forall (k : Clock) a b. (a -> b) -> |>k (Stream k a -> Stream k b) -> Stream k a -> Stream k b.
          let mapfix = \g xs ->
                case unfold xs of
                | Cons x xs' -> 
                  let ys = \\(af : k) -> g [af] (xs' [af])
                  in  cons (f x) ys
          in fix mapfix.

        z : Nat.
        z = fold Z.

        s : Nat -> Nat.
        s = \x -> fold (S x).

        cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
        cons = \x xs -> fold (Cons x xs).

        nats : forall (k : Clock). Stream k Nat.
        nats = fix (\g -> cons z (map (strmap s) g)).

      |]

      takeValueList vnatToInt 10 (evalProg "nats" p) `shouldBe` [0..9]

    it "evals the constant stream" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).

        data NatF f = Z | S f.
        type Nat = Fix NatF.
        
        repeat : forall (k : Clock) a. a -> Stream k a.
        repeat = \x ->
          let body = (\xs -> fold (Cons x xs)) 
          in  fix body.
        
        main : forall (k : Clock). Stream k Nat.
        main = repeat Z.
      |]
      takeValueList vnatToInt 10 (evalProg "main" prog) `shouldBe` (replicate 10 0)

    it "evals the true-false function" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).
        data Bool = True | False.

        cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
        cons = \x xs -> fold (Cons x xs).

        truefalse : forall (k : Clock). Stream k Bool.
        truefalse = fix (\g -> cons True (\\(af : k) -> cons False g)).
      |]

      let truefalse = True : False : truefalse
      takeValueList vboolToBool 10 (evalProg "truefalse" prog) `shouldBe` (take 10 $ truefalse)

    it "evals the every-other function" $ do
      let Right prog = pprog [text|
        data StreamF (k : Clock) a f = Cons a (|>k f).
        type Stream (k : Clock) a = Fix (StreamF k a).
        data CoStream a = Cos (forall (kappa : Clock). Stream kappa a).

        data Bool = True | False.

        truefalse : forall (k : Clock). Stream k Bool.
        truefalse = fix (\g -> cons True (\\(af : k) -> cons False g)).

        cos : forall (k : Clock) a. a -> |>k (CoStream a) -> CoStream a.
        cos = \x xs -> 
          Cos (fold (Cons x (\\(af : k) -> uncos (xs [af])))). -- won't work with map :(

        uncos : forall (k : Clock) a. CoStream a -> Stream k a.
        uncos = \xs -> case xs of | Cos xs' -> xs'.

        cons : forall (k : Clock) a. a -> |>k (Stream k a) -> Stream k a.
        cons = \x xs -> fold (Cons x xs).

        hd : forall a. CoStream a -> a.
        hd = \xs -> 
          let Cos s = xs
          in case unfold s of
             | Cons x xs' -> x.

        -- see if you can do this better with let generalization
        tl : forall a. CoStream a -> CoStream a.
        tl = \x ->
          let Cos s = x in
          let r = (case unfold s of
                  | Cons x xs' -> xs' 
                  ) : forall (k : Clock). |>k (Stream k a)
          in Cos (r [<>]).

        eof : forall (k : Clock) a. |>k (CoStream a -> CoStream a) -> CoStream a -> CoStream a.
        eof = \f xs -> 
          let tl2 = tl (tl xs) in
          let dtl = (\\(af : k) -> (f [af]) tl2) in
          cos (hd xs) dtl.

        eo : forall a. CoStream a -> CoStream a.
        eo = fix eof.

        trues : Stream K0 Bool.
        trues = 
          let Cos xs = eo (Cos truefalse) in
          xs.
      |]
      takeValueList vboolToBool 1000 (evalProg "trues" prog) `shouldBe` (replicate 1000 True)
    
    it "evals fmap" $ do
      let Right prog = pprog [text|
        data NatF a = Z | S a deriving Functor. 
        data Bool = True | False.

        main : Bool.
        main = fmap {NatF} (\x -> True) (S False).
      |]
      let v = evalProg "main" prog
      v `shouldBe` (Constr "S" [Constr "True" []])


    it "evals primitive recursion over natural numbers" $ do
      let Right prog = pprog [text|
        data NatF a = Z | S a deriving Functor.
        type Nat = Fix NatF.

        s : Nat -> Nat.
        s = \x -> fold (S x).

        z : Nat.
        z = fold Z.

        plus : Nat -> Nat -> Nat.
        plus = \m n -> 
          let body = \x ->
            case x of
              | Z -> n
              | S (m', r) -> fold (S r)
          in  primRec {NatF} body m.

        multRec : Nat -> NatF (Nat, Nat) -> Nat.
        multRec = \n x ->
          case x of
            | Z -> fold Z
            | S (m', r) -> plus n r.
        
        mult : Nat -> Nat -> Nat.
        mult = \m n ->
          primRec {NatF} (multRec n) m.
        
        one : Nat.
        one = s z.
        two : Nat.
        two = s one.
        three : Nat.
        three = s two.

        main : Nat.
        main = mult (plus two three) two.
        -- main = plus (s (s (s z))) (s (s z)).
      |]
      {-
      instance Functor NatF where
        fmap f x = case x of
          | Z -> Z
          | S n -> S (f n)

      primRec τ
      => \body z -> body (fmap (\x -> (x, primRec body x))) z

      plus (S Z) (S Z)
      => primRec body (S Z)
      => body (fmap (\x -> (x, primRec body x) (S Z))
      => body (S (S Z, primRec body Z))
      => body (S (S Z, body (fmap (\x -> (x, primRec body x) Z))))
      => body (S (S Z, body Z))
      => body (S (S Z, S Z))
      => body (S (S Z))
      -} 
      let v = evalProg "main" prog
      let n 0 = Constr "Z" []
          n k = Constr "S" [n (k-1)]
      v `shouldBe` n (10 :: Int)
      -- putStrLn (replicate 80 '-')
      -- putStrLn (pps v)
      -- putStrLn (replicate 80 '-')
      -- True `shouldBe` True

  it "evals replaceMin example" $ do
    let Right prog = pprog Fixtures.replaceMin
    let v = evalProg "main" prog
    takeTree v `shouldBe` ofHeight "Z" 5 

  it "evals stream processing example" $ do
    let Right prog = pprog Fixtures.streamProcessing
    let v = evalProg "main" prog
    let conv (Constr "MkUnit" []) = ()
        conv _                   = undefined
    takeValueList conv 10 v `shouldBe` replicate 10 ()
        
data Tree a = Leaf a | Br (Tree a) (Tree a) deriving (Eq, Show)
takeTree :: Value a -> Tree String
takeTree (Constr "Leaf" [Constr "Z" []]) = Leaf "Z"
takeTree (Constr "Br" [t1, t2]) = Br (takeTree t1) (takeTree t2)
takeTree v = error $ pps v

ofHeight :: a -> Int -> Tree a
ofHeight x 0 = Leaf x 
ofHeight x n = Br (ofHeight x (n-1)) (ofHeight x (n-1))


vnatToInt :: Value a -> Int
vnatToInt (Constr "Z" _) = 0
vnatToInt (Constr "S" [v]) = succ (vnatToInt v)
vnatToInt v = error $ "vnatToInt: " ++ pps (takeConstr 10 v)

vboolToBool :: Value a -> Bool
vboolToBool v = 
  case v of
    Constr "True" _ -> True
    Constr "False" _ -> False
    _                -> error $ "vboolToBool error: " ++ pps (takeConstr 10 v)

takeValueList :: (Value a -> b) -> Int -> Value a -> [b]
takeValueList f n v 
  | n <= 0    = []
  | otherwise = 
      case v of
        Constr "Cons" [] -> []
        Constr "Cons" (v':vs) -> f v' : concatMap (takeValueList f (n-1)) vs
        _            -> [f v]
        -- Constr nm vs -> Constr nm (map (takeConstr (n-1)) vs)
        -- Constr nm vs -> Constr nm $ snd (foldr (\v' (n',acc) -> (n' - 1, takeConstr (n' - 1) v' : acc)) (n, []) vs)
        -- _            -> error $ "takeValueList" ++ pps v
