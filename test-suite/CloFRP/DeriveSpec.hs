{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.DeriveSpec where

import Test.Tasty.Hspec
import Data.Maybe (isJust)
import qualified Data.Map.Strict as M
import Data.List (find)

import qualified CloFRP.AST  as E
import qualified CloFRP.AST.Prim    as P
import           CloFRP.AST ((@->:), (@@:), Kind(..))
import           CloFRP.AST (LamCalc(..))
import           CloFRP.Derive
import           CloFRP.Pretty
import           CloFRP.TestUtils
import           CloFRP.Check.TestUtils
import           CloFRP.Annotated
import           CloFRP.Check
import           CloFRP.Check.Prog
import           CloFRP.QuasiQuoter
import           CloFRP.Context
import           CloFRP.Utils
import           CloFRP.Eval

data Ftor0 f = Ftor0 (forall a. (a, f))

instance Functor Ftor0 where
  fmap f (Ftor0 x) = Ftor0 (fst x, f (snd x))

data Ftor1 f = Ftor1 (forall a. a -> f) 
data Ftor2 f = Ftor2 (Int -> f)

instance Functor Ftor1 where
  fmap f (Ftor1 g) = Ftor1 (f . g) -- Ftor1 (\x -> f (g x))

instance Functor Ftor2 where
  fmap f (Ftor2 g) = Ftor2 (\x -> f (g x))

data Ftor3 f = forall a. Ftor3 (a -> f) -- deriving (Functor)

instance Functor Ftor3 where
  fmap f (Ftor3 g) = Ftor3 (\x -> f (g x))

data Ftor4 f = Ftor4 f (Maybe f)

instance Functor Ftor4 where
  fmap f (Ftor4 x my) = Ftor4 (f x) (fmap f my)

data Ftor5 f = Ftor5 ((f -> Int) -> Int)

instance Functor Ftor5 where
  fmap f (Ftor5 a) = Ftor5 (\bf -> a (\x -> bf (f x)))

data Cont r a = Cont ((a -> r) -> r)

instance Functor (Cont r) where
  fmap f (Cont c) = Cont (\c' -> c (\x -> c' (f x)))

runElabProg :: Unann a1 (E.Prog a) => a1 -> Either (TyExcept a) (ElabProg a)
runElabProg p = 
  case runTypingM0 (elabProg . unann $ p) mempty of
    (Right ep, _, _) -> pure ep
    (Left (err,_), _, _) -> Left err


mktr :: Unann p (E.Prog a) => p -> TypingRead a
mktr p = 
  let (Right (ElabProg { kinds, destrs, types }), _, _) = runTypingM0 (elabProg . unann $ p) mempty
  in  mempty { trKinds = kinds, trDestrs = destrs, trFree = types }

fmapt :: String -> [String] -> E.Type () 'E.Poly -> E.Type () 'E.Poly
fmapt f b con = E.forAll (b ++ [f, "#b"]) $ (E.tvar f @->: "#b") @->: con @@: E.tvar f @->: con @@: "#b"

deriveFunctorAndExtract :: E.Datatype a -> Either String (E.Type a 'E.Poly, E.Expr a)
deriveFunctorAndExtract dt = 
  case deriveFunctor dt of
    Left err -> Left err
    Right (ClassInstance {ciDictionary}) ->
      case M.lookup "fmap" ciDictionary of 
        Nothing -> Left "didnt even find fmap"
        Just r -> Right r

deriveSpec :: Spec
deriveSpec = do
  describe "deriveFunctor" $ do
    let bindp x = E.bind . E.UName $ ("#" ++ show (x :: Int))
    let bindpm  = E.bind . E.MName
    let varm x  = E.var . E.UName $ ("#" ++ show (x :: Int))

    it "derives peano numerals functor" $ do
      let dt = E.Datatype
            { E.dtName = "NatF"
            , E.dtBound = [("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Z" []
              , A () $ E.Constr "S" ["f"]
              ]
            }
      let Right (fmapTy, fmapDef) = deriveFunctorAndExtract dt
      fmapDef `shouldBe` 
        ("#f" @-> "#val" @-> 
          E.caseof "#val" 
            [ (E.match "Z" [], "Z")
            , (E.match "S" [bindp 0], "S" @@ ("#f" @@ varm 0))
            ]
        )

      fmapTy `shouldBe` fmapt "f" [] "NatF"
      let tr = mktr [unsafeProg|data NatF f = Z | S f.|]
      runCheck tr fmapDef fmapTy `shouldYield` mempty

    it "derives list functor" $ do
      let dt = E.Datatype
            { E.dtName = "ListF"
            , E.dtBound = [("a", E.Star), ("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Nil" []
              , A () $ E.Constr "Cons" ["a", "f"]
              ]
            }
      let Right (fmapTy, fmapDef) = deriveFunctorAndExtract dt
      fmapDef `shouldBe` 
        ("#f" @-> "#val" @-> 
          E.caseof "#val" 
            [ (E.match "Nil" [], "Nil")
            , (E.match "Cons" [bindp 0, bindp 1], "Cons" @@ (("x" @-> "x") @@ varm 0) @@ ("#f" @@ varm 1))
            ]
        )

      fmapTy `shouldBe` fmapt "f" ["a"] ("ListF" @@: "a")
      let tr = mktr [unsafeProg|data ListF a f = Nil | Cons a f.|]
      runCheck tr fmapDef fmapTy `shouldYield` mempty
    
    it "derives functor for tuple data-type" $ do
      let dt = E.Datatype
            { E.dtName = "Pair"
            , E.dtBound = [("a", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Pair" [E.tTup ["a", "a"]]
              ]
            }

      let Right (fmapTy, fmapDef) = deriveFunctorAndExtract dt
      let inner = "x" @-> E.caseof "x" [E.pTup [bindp 0, bindp 1] |-> E.tup ["#f" @@ varm 0, "#f" @@ varm 1]]
      fmapDef `shouldBe` 
        ("#f" @-> "#val" @-> 
          E.caseof "#val" 
            [ E.match "Pair" [bindp 0] |-> "Pair" @@ (inner @@ varm 0) ]
        )

      fmapTy `shouldBe` fmapt "a" [] "Pair"
      let tr = mktr [unsafeProg|data Pair a = Pair (a,a). |]
      runCheck tr fmapDef fmapTy `shouldYield` mempty

    it "derives functor for strictly positive type-var (1)" $ do
      let dt = E.Datatype
            { E.dtName = "Pos"
            , E.dtBound = [("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Pos" ["Unit" @->: "f"]
              ]
            }
      {-
      it derives to
      Pos ((\x b -> #f (x (id b))) `a)
      => Pos ((\x b -> #f (x b)) `a)
      => Pos (\b -> #f (`a b))
      Pos (\b -> #f (`a b))
      -}
      case deriveFunctorAndExtract dt of
        Left err -> failure err
        Right (fmapTy, fmapDef) -> do
          fmapDef `shouldBe` 
            ("#f" @-> "#val" @-> 
              E.caseof "#val" 
                [ (E.match "Pos" [bindp 0], "Pos" @@ (("x" @-> "b" @-> "#f" @@ ("x" @@ (("x" @-> "x") @@ "b"))) @@ varm 0))
                ]
            )
          fmapTy `shouldBe` fmapt "f" [] "Pos"
          let tr = mktr [unsafeProg|data Unit = Unit. data Pos f = Pos (Unit -> f).|]
          runCheck tr fmapDef fmapTy `shouldYield` mempty

    it "cannot derive functor for negative type-var (1)" $ do
      let dt = E.Datatype
            { E.dtName = "Neg"
            , E.dtBound = [("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Pos" ["f" @->: "Int"]
              ]
            }
      case deriveFunctorAndExtract dt of
        Left err -> err `shouldBe` "type variable f is in a negative position"
        Right (fmapTy, fmapDef) -> failure ("got " ++ pps fmapDef ++ " but expected failure")

    it "cannot derive functor for negative type-var (2)" $ do
      let dt = E.Datatype
            { E.dtName = "Neg"
            , E.dtBound = [("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Pos" [("Int" @->: "f") @->: "Int"]
              ]
            }
      case deriveFunctorAndExtract dt of
        Left err -> err `shouldBe` "type variable f is in a negative position"
        Right (fmapTy, fmapDef) -> failure ("got " ++ pps fmapDef ++ " but expected failure")

    it "derives functor for strictly positive type-var (2)" $ do
      let dt = E.Datatype
            { E.dtName = "Pos"
            , E.dtBound = [("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Pos" [("f" @->: "Unit") @->: "Unit"]
              ]
            }
      {-
      Pos ((\x b -> 
            (\x -> x) (x ((\x b -> (\x -> x) (x (#f b))) b)))
          `a
          )
      =>
      Pos ((\b -> (`a (\b' -> b (#f b')))))
      -}
      case deriveFunctorAndExtract dt of
        Left err -> failure err
        Right (fmapTy, fmapDef) -> do
          let ide = "x" @-> "x"
              bd = ide @@ ("x" @@ (("x" @-> "b" @-> ide @@ ("x" @@ ("#f" @@ "b"))) @@ "b"))
              fn = "x" @-> "b" @-> bd
              pos = fn @@ varm 0
          fmapDef `shouldBe` 
            ("#f" @-> "#val" @-> 
              E.caseof "#val" 
                [ (E.match "Pos" [bindp 0], "Pos" @@ pos)
                ]
            )
          fmapTy `shouldBe` fmapt "f" [] "Pos"
          let tr = mktr [unsafeProg|data Unit = Unit. data Pos f = Pos ((f -> Unit) -> Unit).|]
          runCheck tr fmapDef fmapTy `shouldYield` mempty

    it "derives functor for continuations" $ do
      let dt = E.Datatype
            { E.dtName = "Cont"
            , E.dtBound = [("r", E.Star), ("a", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Cont" [("a" @->: "r") @->: "r"]
              ]
            }
      case deriveFunctorAndExtract dt of
        Left err -> failure err
        Right (fmapTy, fmapDef) -> do
          let ide = "x" @-> "x"
              bd = ide @@ ("x" @@ (("x" @-> "b" @-> ide @@ ("x" @@ ("#f" @@ "b"))) @@ "b"))
              fn = "x" @-> "b" @-> bd
              pos = fn @@ varm 0
          fmapDef `shouldBe` 
            ("#f" @-> "#val" @-> 
              E.caseof "#val" 
                [ (E.match "Cont" [bindp 0], "Cont" @@ pos)
                ]
            )
          fmapTy `shouldBe` fmapt "a" ["r"] ("Cont" @@: "r")
          let tr = mktr [unsafeProg|data Cont r a = Cont ((a -> r) -> r).|]
          runCheck tr fmapDef fmapTy `shouldYield` mempty

  describe "deriving in elabProg" $ do
    it "works for simple example " $ do
      let Right ep = runElabProg [unsafeProg|
        data NatF f = Z | S f deriving Functor.
        data ListF a f = Nil | Cons a f deriving (Functor).
      |]
      let Just ftors = query "Functor" (instances ep)
      let natf = (ftors !! 0)
      let listf = (ftors !! 0)
      ciClassName natf `shouldBe` "Functor"
      fst <$> M.lookup "fmap" (ciDictionary natf) `shouldBe` Just (fmapt "f" [] "NatF")
      ciClassName listf `shouldBe` "Functor"
      fst <$> M.lookup "fmap" (ciDictionary listf) `shouldBe` Just (fmapt "f" [] "NatF")

    it "works for type with forall-quantification" $ do
      let v = evalProg "main" [unsafeProg|
        data Foo a = Foo (forall b. b -> (a,b)) deriving Functor.
        data A = A.
        data B = B.

        main : Foo B.
        main = case fmap {Foo} (\x -> B) (Foo (\x -> (A, x))) of
          | Foo fn -> fn B.
      |]
      v `shouldBe` Tuple [Constr "B" [], Constr "B" []]

    it "works for nested functors" $ do
      let prog = [unsafeProg|
        data F1 a = F1 a deriving Functor.
        data F2 a = F2 (F1 a) deriving Functor.
        data A = MkA. data B = MkB.

        main : F2 B.
        main = fmap {F2} (\x -> MkB) (F2 (F1 MkA)).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "works for nested functors and type aliases" $ do
      let prog = [unsafeProg|
        data F1 a = F1 a deriving Functor.
        type F1' a = F1 a.
        data F2 a = F2 (F1' a) deriving Functor.
        data A = MkA. data B = MkB.

        main : F2 B.
        main = fmap {F2} (\x -> MkB) (F2 (F1 MkA)).
      |]
      runCheckProg mempty prog `shouldYield` ()
      evalProg "main" prog `shouldBe` Constr "F2" [Constr "F1" [Constr "MkB" []]]

    -- it "works for recursive types (Nat)" $ do
    --   let prog = [unsafeProg|
    --     data NatF f = Z | S f deriving Functor.
    --     data Nat = Nat (Fix NatF) deriving Functor.

    --     z : Nat.
    --     z = Nat (fold Z).
    --     s : Nat -> Nat.
    --     s = \x -> Nat (fold (S x)).

    --     main : Nat.
    --     main = fmap {Nat} (\x -> x) (s (s (s z))).
    --   |]
    --   runCheckProg mempty prog `shouldYield` ()
      -- let moreList x y = Constr "MoreList" [x ,y]
      -- let nil = Fold (Constr "Nil" [])
      -- let cons x xs = Fold (Constr "Cons" [x, xs])
      -- let mka = Constr "MkA" []
      -- let mkb = Constr "MkB" []

      -- let v = evalProg "main" prog
      -- v `shouldBe` moreList mkb (cons mkb (cons mkb (cons mkb nil)))

    -- it "works for recursive types (List)" $ do
    --   let prog = [unsafeProg|
    --     data ListF a f = Nil | Cons a f deriving Functor.
    --     type List a = Fix (ListF a).
    --     data List' a = List' (List a) deriving Functor.
    --     data A = A. data B = B.

    --     cons : forall a. a -> List a -> List a.
    --     cons = \x xs -> fold (Cons x xs).

    --     nil : forall a. List a.
    --     nil = fold Nil.

    --     as : List' A.
    --     as = List' (cons A (cons A (cons A nil))).

    --     main : List' B.
    --     main = fmap {List'} (\x -> B) as.
    --   |]
    --   runCheckProg mempty prog `shouldYield` ()
      -- let moreList x y = Constr "MoreList" [x ,y]
      -- let nil = Fold (Constr "Nil" [])
      -- let cons x xs = Fold (Constr "Cons" [x, xs])
      -- let mka = Constr "MkA" []
      -- let mkb = Constr "MkB" []

    --   let v = evalProg "main" prog
    --   v `shouldBe` moreList mkb (cons mkb (cons mkb (cons mkb nil)))

    it "doesnt work for type with wrong kind" $ do
      let Left err = runElabProg [unsafeProg|
        data FooF (f : * -> *) = Foo (forall a. f a) deriving Functor.
      |]
      err `shouldBe` Other "f must have kind * but had kind * -> *"