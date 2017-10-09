{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module CloTT.Check.Poly.ProgSpec where

import Test.Tasty.Hspec

import           CloTT.Check.Poly.TestUtils
import           CloTT.QuasiQuoter
import           CloTT.Check.Poly.Prog
import           CloTT.Check.Poly.TypingM

progSpec :: Spec 
progSpec = do
  describe "checkProg" $ do
    it "fails programs with invalid types (1)" $ do
      let prog = [unsafeProg|
        data Foo a = MkFoo a.
        foo : Foo -> Nat.
        foo = \x -> x.
      |]
      shouldFail $ runCheckProg mempty prog

    it "succeeds for mono-types" $ do
      let prog = [unsafeProg|
        data Int = .
        data IntList = Nil | Cons Int IntList.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "fails programs with invalid types (2)" $ do
      let prog = [unsafeProg|
        data List a = Nil | Cons a (List a a).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails programs with invalid types (3)" $ do
      let prog = [unsafeProg|
        data List = Nil | Cons a (List a).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "succeeds for some simple functions" $ do
      let prog = [unsafeProg|
        data Unit = Unit.
        foo : Unit -> Unit.
        foo = \x -> x.
        app : (Unit -> Unit) -> Unit -> Unit.
        app = \f -> \x -> f x.
        bar : Unit.
        bar = app foo Unit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for some simple poly functions" $ do
      let prog = [unsafeProg|
        foo : forall a. a -> a.
        foo = \x -> x.
        app : forall a b. (a -> b) -> a -> b.
        app = \f -> \x -> f x.
        data Unit = Unit.
        bar : Unit.
        bar = app foo Unit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for monomorphic patterns (1)" $ do
      let prog = [unsafeProg|
        data FooBar = Foo | Bar.
        data Two = One | Two.
        foo : FooBar -> Two.
        foo = \x ->
          case x of
            | Foo -> One
            | Bar -> Two.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for monomorphic patterns (2)" $ do
      let prog = [unsafeProg|
        data FooBar = Foo | Bar.
        data Two = One FooBar | Two.
        foo : FooBar -> Two.
        foo = \x ->
          case x of
            | Foo -> One x
            | Bar -> Two.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "suceeds for polymorphic patterns (1)" $ do
      let prog = [unsafeProg|
        data Maybe a = Nothing | Just a.
        data Int = .
        data FooBar = Foo Int | Bar.
        m1 : forall a. Maybe a.
        m1 = Nothing.

        isFoo : FooBar -> Maybe Int.
        isFoo = \x ->
          case x of
            | Foo i -> Just i
            | Bar -> Nothing.
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "suceeds for simple poly pattern match (Wrap)" $ do
      let prog = [unsafeProg|
        data Wrap t = MkWrap t.
        unWrap : forall a. Wrap a -> a.
        unWrap = \x ->
          case x of
            | MkWrap x' -> x'.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "suceeds for nested poly pattern match (Wrap)" $ do
      let prog = [unsafeProg|
        data Wrap t = MkWrap t.
        unUnWrap : forall a. Wrap (Wrap a) -> a.
        unUnWrap = \x ->
          case x of
            | MkWrap (MkWrap x') -> x'.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for not-deep-enough pattern matches" $ do
      let prog = [unsafeProg|
        data Wrap t = MkWrap t.
        unUnWrap : forall a. Wrap (Wrap a) -> a.
        unUnWrap = \x ->
          case x of
            | MkWrap x' -> x'.
      |]
      shouldFail $ runCheckProg mempty prog

    it "succeeds for nested list matching" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Maybe a = Nothing | Just a.
        head2 : forall a. List a -> Maybe a.
        head2 = \xs -> 
          case xs of
            | Cons x (Cons x' xs') -> Just x'
            | xs' -> Nothing.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for lists and and maybe" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        singleton : forall a. a -> List a.
        singleton = \x -> Cons x Nil.

        data Maybe a = Nothing | Just a.
        head : forall a. List a -> Maybe a.
        head = \xs -> 
          case xs of
            | Nil -> Nothing
            | Cons x xs' -> Just x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for rank2 crap" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Unit = MkUnit.
        foo : (forall a. List a) -> Unit.
        foo = \xs ->
          case xs of
            | Nil -> MkUnit
            | Cons x xs -> x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for rank2 crap" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Unit = MkUnit.
        data Either a b = Left a | Right b.
        data Bool = True | False.
        foo : (forall a. List a) -> Either Unit Bool.
        foo = \xs ->
          case xs of
            | Cons x Nil -> Left x
            | Cons x Nil -> Right x.
      |]
      -- runCheckProg mempty prog `shouldYield` ()
      shouldFail $ runCheckProg mempty prog 

    it "suceeds for rank2 stuff" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).
        data Pair a b = Pair a b.
        data Bool = True | False.
        data Unit = Unit.
        foo : (forall a. a -> a) -> Pair (List Bool) (Unit).
        foo = \id ->
          Pair (Cons (id True) Nil) (id Unit).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for tricky polymorphism (1)" $ do
      let prog = [unsafeProg|
        data List t = Nil | Cons t (List t).

        data Maybe a = Nothing | Just a.
        head : forall a b. List a -> Maybe b.
        head = \xs -> 
          case xs of
            | Nil -> Nothing
            | Cons x xs' -> Just x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails getRight" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        getRight : forall a b. Either a b -> b.
        getRight = \e ->
          case e of
            | Left x -> x
            | Right x -> x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for tricky polymorphism (2)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall a b. Either a b -> Maybe a.
        toMaybe = \e ->
          case e of
            | Left x -> Nothing
            | Right x -> Just x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for wrong patterns" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall a b. Either a b -> Maybe a.
        toMaybe = \e ->
          case e of
            | Left x -> Nothing
            | Just x -> Just x.
      |]
      shouldFail $ runCheckProg mempty prog 
    
    it "fails for impredicative types" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall b. Either (forall a. a) b -> b.
        toMaybe = \e ->
          case e of
            | Left x -> x
            | Just x -> x.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "succeeds for toMaybe" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Maybe a = Nothing | Just a.

        toMaybe : forall a b. Either a b -> Maybe b.
        toMaybe = \e ->
          case e of
            | Left x -> Nothing
            | Right x -> Just x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "suceeds for polymorphic function composition" $ do
      let prog = [unsafeProg|

        compose : forall a b c. (b -> c) -> (a -> b) -> (a -> c).
        compose = \g -> \f -> \x -> g (f x).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "infers the type of lambdas" $ do
      let prog = [unsafeProg|

        data Bool = True | False.
        data Unit = MkUnit.
        test : Bool -> Unit.
        test = \x -> (\x' -> MkUnit) x.

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "suceeds for contravariant functor" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Predicate a = Pred (a -> Bool).

        comap : forall a b. (b -> a) -> Predicate a -> Predicate b.
        comap = \fn -> \pred -> 
          case pred of
            | Pred fn' -> Pred (\x -> fn' (fn x)).
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for lefts" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Either a b = Left a | Right b.
        data List a = Nil | Cons a (List a).

        lefts : forall a b. List (Either a b) -> List a.
        lefts = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Left x) xs'  -> Cons x (lefts xs')
            | Cons (Right x) xs' -> lefts xs'.

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for incorrect rights" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Either a b = Left a | Right b.
        data List a = Nil | Cons a (List a).

        rights : forall a b. List (Either a b) -> List b.
        rights = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Left x) xs'  -> Cons x (rights xs')
            | Cons (Right x) xs' -> rights xs'.
      |]
      shouldFail $ runCheckProg mempty prog

    -- we need a new rule to instantiate existentials with type-applications
    it "succeeds for a bunch of eithers" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data Unit = MkUnit.
        data A = MkA.
        data B = MkB.

        either1 : Either (Either Unit Unit) Unit.
        either1 = Left (Left MkUnit).
        either2 : Either (Either B A) A.
        either2 = Left (Right MkA).
        either3 : Either (Either B A) A.
        either3 = Left (Left MkB).
        either4 : Either (Either B A) A.
        either4 = Right MkA.
      |]
      runCheckProg mempty prog `shouldYield` ()


    it "succeeds for a bunch of polymorphic eithers" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.

        either1 : forall a b c. a -> Either a (Either b c).
        either1 = \a -> Left a.
        either2 : forall a. a -> Either a (Either a a).
        either2 = \a -> Left a.
        either3 : forall a b c. a -> Either (Either a b) c.
        either3 = \a -> Left (Left a).
        either4 : forall a b c. b -> Either (Either a b) c.
        either4 = \a -> Left (Right a).
        either5 : forall a b c d. b -> Either (Either a b) (Either c d).
        either5 = \a -> Left (Right a).
        either6 : forall a b c d e. b -> Either (Either a (Either b c)) (Either d e).
        either6 = \a -> Left (Right (Left a)).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for nested eithers (either-swap)" $ do
      let prog = [unsafeProg|
        data Bool = True | False.
        data Either a b = Left a | Right b.

        main : forall a b c d. Either (Either a b) (Either c d) -> Either (Either d c) (Either b a).
        main = \e1 ->
          case e1 of
            | Left  (Left  a) -> Right (Left a)
            | Left  (Right b) -> Right (Right b)
            | Right (Left  c) -> Left  (Right c)
            | Right (Right d) -> Left  (Left d).
      |]
      shouldFail $ runCheckProg mempty prog

    it "fails for a bunch of eithers (1)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data A = MkA.
        data B = MkB.

        either : Either (Either B A) A.
        either = Left (Left MkA).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for a bunch of eithers (2)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data A = MkA.
        data B = MkB.

        either : Either A (Either B A).
        either = Right (Left MkA).
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails for a bunch of eithers (3)" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.

        either : forall a b c. a -> Either a (Either b c).
        either = \x -> Right (Left x).
      |]
      shouldFail $ runCheckProg mempty prog 
    
    it "suceeds for church lists (data-dec)" $ do
      let prog = [unsafeProg|
        data ChurchList a = ChurchList (forall r. (a -> r -> r) -> r -> r).
        data List a = Nil | Cons a (List a).
        
        runList : forall a. ChurchList a -> forall r. (a -> r -> r) -> r -> r.
        runList = \cl ->
          case cl of
            | ChurchList fn -> fn.
        
        -- | Make a 'ChurchList' out of a regular list.
        -- fromList : forall a. List a -> ChurchList a.
        -- fromList xs = ChurchList (\k -> \z -> foldr k z xs
        
        -- | Turn a 'ChurchList' into a regular list.
        toList : forall a. ChurchList a -> List a.
        toList = \xs -> runList xs Cons Nil.
        
        -- | The 'ChurchList' counterpart to '(:)'.  Unlike 'DList', whose
        -- implementation uses the regular list type, 'ChurchList' abstracts
        -- over it as well.
        cons : forall a. a -> ChurchList a -> ChurchList a.
        cons = \x xs -> ChurchList (\k z -> k x (runList xs k z)).
        
        -- | Append two 'ChurchList's.  This runs in O(1) time.  Note that
        -- there is no need to materialize the lists as @[a]@.
        append : forall a. ChurchList a -> ChurchList a -> ChurchList a.
        append = \xs ys -> ChurchList (\k z -> runList xs k (runList ys k z)).
        
        -- i.e.,
        
        nil : forall a. ChurchList a.
        nil = ChurchList (\k z -> z).
        
        singleton : forall a. a -> ChurchList a.
        singleton = \x -> ChurchList (\k z -> k x z).

        snoc : forall a. ChurchList a -> a -> ChurchList a.
        snoc = \xs x -> ChurchList (\k z -> runList xs k (k x z)).
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "succeeds for church lists (alias)" $ do
      let prog = [unsafeProg|
        data List a = Nil | Cons a (List a).
        type ChurchList a = forall r. (a -> r -> r) -> r -> r.
        
        cons : forall a. a -> ChurchList a -> ChurchList a.
        cons = \x xs -> \k z -> k x (xs k z).

        toList : forall a. ChurchList a -> List a.
        toList = \xs -> xs Cons Nil.

        append : forall a. ChurchList a -> ChurchList a -> ChurchList a.
        append = \xs ys -> \k z -> xs k (ys k z).
        
        nil : forall a. ChurchList a.
        nil = \k z -> z.
        
        singleton : forall a. a -> ChurchList a.
        singleton = \x -> \k z -> k x z.

        snoc : forall a. ChurchList a -> a -> ChurchList a.
        snoc = \xs x -> \k z -> xs k (k x z).
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for Data.Either stdlib" $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        data List a = Nil | Cons a (List a).
        data Bool = True | False.
        data Pair a b = MkPair a b.

        either : forall a b c. (a -> c) -> (b -> c) -> Either a b -> c.
        either = \lf rf e ->
          case e of
            | Left l -> lf l
            | Right r -> rf r.
        
        lefts : forall a b. List (Either a b) -> List a.
        lefts = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Left x) xs'  -> Cons x (lefts xs')
            | Cons (Right x) xs' -> lefts xs'.

        rights : forall a b. List (Either a b) -> List b.
        rights = \xs ->
          case xs of
            | Nil -> Nil
            | Cons (Right x) xs' -> Cons x (rights xs')
            | Cons (Left x) xs'  -> rights xs'.
        
        partitionEithers : forall a b. List (Either a b) -> Pair (List a) (List b).
        partitionEithers = \xs ->
          case xs of
            | Nil -> MkPair Nil Nil
            | Cons x xs' -> 
              case (partitionEithers xs') of
                | MkPair ls rs ->
                  case x of
                    | Left x' -> MkPair (Cons x' ls) rs
                    | Right x' -> MkPair ls (Cons x' rs).
        
        isLeft : forall a b. Either a b -> Bool.
        isLeft = \e ->
          case e of
            | Left x -> True
            | Right x -> False.

        isRight : forall a b. Either a b -> Bool.
        isRight = \e ->
          case e of
            | Left x -> False
            | Right x -> True.
        
        fromLeft : forall a b. a -> Either a b -> a.
        fromLeft = \d e ->
          case e of
            | Left x -> x
            | Right x -> d.

        fromRight : forall a b. b -> Either a b -> b.
        fromRight = \d e ->
          case e of
            | Left x -> d
            | Right x -> x.
        
      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "succeeds for superfluous quantifiers" $ do
      let prog = [unsafeProg|
        foo : forall a b c. a -> a.
        foo = \x -> x.

        data Unit = MkUnit.
        bar : Unit.
        bar = foo MkUnit.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails for impossible defs" $ do
      let prog = [unsafeProg|
        foo : forall a b. a -> b.
        foo = \x -> x.
      |]
      shouldFail $ runCheckProg mempty prog 
    
    it "succeeds for non-regular data (omg)" $ do
      let prog = [unsafeProg|
        data Pair a = MkPair a a.
        data BalTree a = Empty | Branch a (BalTree (Pair a)).
        data Nat = Z | S Nat.

        zero : Nat.
        zero = Z.
        one : Nat.
        one = S zero.
        two : Nat.
        two = S one.
        three : Nat.
        three = S two.

        ex01 : forall a. BalTree a.
        ex01 = Empty.

        ex02 : BalTree Nat.
        ex02 = Branch zero Empty.

        ex03 : BalTree Nat.
        ex03 = Branch zero (Branch (MkPair one two) Empty).

        ex04 : BalTree Nat.
        ex04 =
          Branch
            zero 
            (Branch
              (MkPair one two)
              (Branch
                (MkPair (MkPair three three) (MkPair three three))
                Empty
              )
             ).
        
        ofDepth : forall a. a -> Nat -> BalTree a.
        ofDepth = \x n ->
          case n of
            | Z -> Empty
            | S n' -> Branch x (ofDepth (MkPair x x) n').

      |]
      runCheckProg mempty prog `shouldYield` ()
    
    it "checks and expands type-aliases (1) " $ do
      let prog = [unsafeProg|
        data Bar = Bar.
        type Foo = Bar.
        id : Foo -> Bar.
        id = \x -> x. 
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "checks and expands type-aliases (2) " $ do
      let prog = [unsafeProg|
        type Id a = a.
        id : forall a. Id a -> Id a.
        id = \x -> x. 
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "checks and expands type-aliases (3) " $ do
      let prog = [unsafeProg|
        data Either a b = Left a | Right b.
        type FlipSum a b = Either b a.

        flip : forall a b. Either a b -> FlipSum a b.
        flip = \e ->
          case e of
            | Left x -> Right x
            | Right x -> Left x.
      |]
      runCheckProg mempty prog `shouldYield` ()

    it "checks and expands '2nd-order' type-aliases (4)" $ do
      let prog = [unsafeProg|
        data List a = Nil | Cons a (List a).
        type Array a = List a.
        type Array2D a = Array (Array a).

        app : forall a. List a -> List a -> List a.
        app = \xs -> \ys ->
          case xs of
            | Nil -> ys
            | Cons x xs' -> Cons x (app xs' ys).

        flatten : forall a. Array2D a -> Array a.
        flatten = \xss ->
          case xss of
            | Nil -> Nil
            | Cons xs xss' -> app xs (flatten xss').

      |]
      runCheckProg mempty prog `shouldYield` ()

    it "fails incorrect aliases (1)" $ do
      let prog = [unsafeProg|
        type Foo = Bar.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails incorrect aliases (2)" $ do
      let prog = [unsafeProg|
        type A1 = Foo.
        type A2 = A1.
      |]
      shouldFail $ runCheckProg mempty prog 

    it "fails incorrect aliases (3)" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        data Foo a = Foo a.
        type A = Unit -> Foo.
      |]
      shouldFail $ runCheckProg mempty prog 



    it "rejects recursive type aliases" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        data Pair a b = MkPair a b.
        data List a = Nil | Cons a (List a).

        type Units = Pair Unit Units.

        units2lst : Units -> List Unit.
        units2lst = \x ->
          case x of
            | MkPair u us -> Cons u (units2lst us).

      |]
      runCheckProg mempty prog `shouldFailWith` (\(e,_) -> e `shouldBe` Other "Units is recursive")

    it "rejects mutually recursive type aliases" $ do
      let prog = [unsafeProg|
        data Unit = MkUnit.
        data Bool = True | False.
        data Pair a b = MkPair a b.

        type BoolThenUnits = Pair Bool UnitThenBools.
        type UnitThenBools = Pair Unit BoolThenUnits.

      |]
      runCheckProg mempty prog `shouldFailWith` (\(e,_) -> e `shouldBe` Other "BoolThenUnits is recursive")
    
    -- it "succeeds for higher-kinded types" $ do
    --   let prog = [unsafeProg|
    --     data Functor f = Functor (forall a b. (a -> b) -> f a -> f b) .
    --   |]
    --   pending
      -- runCheckProg mempty prog `shouldYield` ()