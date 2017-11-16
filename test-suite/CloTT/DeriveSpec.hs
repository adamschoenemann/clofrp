{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}

module CloTT.DeriveSpec where

import Test.Tasty.Hspec
import Data.Maybe (isJust)
import qualified Data.Map.Strict as M

import qualified CloTT.AST.Parsed  as E
import qualified CloTT.AST.Prim    as P
import           CloTT.AST.Parsed ((@->:), (@@:), Kind(..))
import           CloTT.AST.Parsed (LamCalc(..))
import           CloTT.Derive
import           CloTT.Pretty
import           CloTT.TestUtils
import           CloTT.Check.TestUtils
import           CloTT.Annotated
import           CloTT.Check
import           CloTT.Check.Prog
import           CloTT.QuasiQuoter
import           CloTT.Context

data Ftor0 f = Ftor0 (forall a. (a, f))

instance Functor Ftor0 where
  fmap f (Ftor0 x) = Ftor0 (fst x, f (snd x))

data Ftor1 f = Ftor1 (forall a. a -> f) 
data Ftor2 f = Ftor2 (Int -> f)

instance Functor Ftor1 where
  fmap f (Ftor1 g) = Ftor1 (\x -> f (g x))

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

runElabProg p = 
  case runTypingM0 (elabProg . unann $ p) mempty of
    (Right ep, _, _) -> pure ep
    (Left err, _, _) -> fail (show err)


mktr p = 
  let (Right (ElabProg { kinds, destrs, types }), _, _) = runTypingM0 (elabProg . unann $ p) mempty
  in  mempty { trKinds = kinds, trDestrs = destrs, trFree = types }

fmapt b con = E.forAll (b ++ ["#a", "#b"]) $ ("#a" @->: "#b") @->: con @@: "#a" @->: con @@: "#b"

deriveSpec :: Spec
deriveSpec = do
  describe "deriveFunctor" $ do
    let bindp x = E.bind . E.UName $ ("#" ++ show (x :: Int))
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
      let Right (fmapNm, fmapTy, fmapDef) = deriveFunctor dt
      fmapDef `shouldBe` 
        ("#f" @-> "#val" @-> 
          E.caseof "#val" 
            [ (E.match "Z" [], "Z")
            , (E.match "S" [bindp 0], "S" @@ ("#f" @@ varm 0))
            ]
        )

      fmapTy `shouldBe` fmapt [] "NatF"
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
      let Right (fmapNm, fmapTy, fmapDef) = deriveFunctor dt
      fmapDef `shouldBe` 
        ("#f" @-> "#val" @-> 
          E.caseof "#val" 
            [ (E.match "Nil" [], "Nil")
            , (E.match "Cons" [bindp 0, bindp 1], "Cons" @@ (("x" @-> "x") @@ varm 0) @@ ("#f" @@ varm 1))
            ]
        )

      fmapTy `shouldBe` fmapt ["a"] ("ListF" @@: "a")
      let tr = mktr [unsafeProg|data ListF a f = Nil | Cons a f.|]
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
      case deriveFunctor dt of
        Left err -> failure err
        Right (fmapNm, fmapTy, fmapDef) -> do
          fmapDef `shouldBe` 
            ("#f" @-> "#val" @-> 
              E.caseof "#val" 
                [ (E.match "Pos" [bindp 0], "Pos" @@ (("x" @-> "b" @-> "#f" @@ ("x" @@ (("x" @-> "x") @@ "b"))) @@ varm 0))
                ]
            )
          fmapTy `shouldBe` fmapt [] "Pos"
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
      case deriveFunctor dt of
        Left err -> err `shouldBe` "type variable f is in a negative position"
        Right (fmapNm, fmapTy, fmapDef) -> failure ("got " ++ pps fmapDef ++ " but expected failure")

    it "cannot derive functor for negative type-var (2)" $ do
      let dt = E.Datatype
            { E.dtName = "Neg"
            , E.dtBound = [("f", E.Star)]
            , E.dtDeriving = ["Functor"]
            , E.dtConstrs =
              [ A () $ E.Constr "Pos" [("Int" @->: "f") @->: "Int"]
              ]
            }
      case deriveFunctor dt of
        Left err -> err `shouldBe` "type variable f is in a negative position"
        Right (fmapNm, fmapTy, fmapDef) -> failure ("got " ++ pps fmapDef ++ " but expected failure")

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
      case deriveFunctor dt of
        Left err -> failure err
        Right (fmapNm, fmapTy, fmapDef) -> do
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
          fmapTy `shouldBe` fmapt [] "Pos"
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
      case deriveFunctor dt of
        Left err -> failure err
        Right (fmapNm, fmapTy, fmapDef) -> do
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
          fmapTy `shouldBe` fmapt ["r"] ("Cont" @@: "r")
          let tr = mktr [unsafeProg|data Cont r a = Cont ((a -> r) -> r).|]
          runCheck tr fmapDef fmapTy `shouldYield` mempty

  describe "deriving in elabProg" $ do
    it "works for simple example " $ do
      ep <- runElabProg [unsafeProg|
        data NatF f = Z | S f deriving Functor.
        data ListF a f = Nil | Cons a f deriving (Functor).
      |]
      query "NatF_fmap" (types ep) `shouldBe` Just (fmapt [] "NatF")
      M.lookup "NatF_fmap" (defs ep) `shouldSatisfy` isJust
      query "ListF_fmap" (types ep) `shouldBe` Just (fmapt ["a"] $ "ListF" @@: "a")
      M.lookup "ListF_fmap" (defs ep) `shouldSatisfy` isJust