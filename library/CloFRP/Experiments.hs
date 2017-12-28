{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}


module CloFRP.Experiments where
-- This is just to keep some experiments around

-- Primitive recursion encoded with functors

-- F[μX. F[X]] -> (μX. F[X])
data Fix f = Into (f (Fix f))

-- (μX. F[X]) -> F[μX. F[X]]
out :: Fix f -> f (Fix f)
out (Into f) = f

data NatF a = Z | S a deriving Show

instance Functor NatF where
  fmap f Z = Z
  fmap f (S n) = S (f n)

instance Show (Fix NatF) where
  show = show . toInt

-- instance Functor NatF where
--   fmap f x = 
--     case x of
--       Z -> Z
--       S x' -> S (f x')

type Nat = Fix NatF

zero :: Nat
zero = Into Z

-- just for inspiration (general recursion fixpoint)
fix :: (a -> a) -> a 
fix f =
  let x = f x
  in x


pred :: Nat -> Nat
pred m =
  case out m of
    Z -> Into Z
    S m' -> m'

pred2 :: Nat -> Nat
pred2 m = 
  case out m of
    S m' -> 
      case out m' of
        S m'' -> m''
        Z     -> Into Z
    Z -> Into Z

-- primitive recursion 
-- (F[(µX. F) × A] → A) → µX. F[X] → A
primRec :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
primRec fn (Into f) =
  fn (fmap (\y -> (y, primRec fn y)) f)

-- plus defined with primitive recursion
plus :: Nat -> Nat -> Nat 
plus m n = primRec fn m where
  fn :: NatF (Nat, Nat) -> Nat 
  fn Z = n
  fn (S (m', r)) = Into (S r)

natId :: Nat -> Nat
natId = primRec fn where
  fn :: NatF (Nat, Nat) -> Nat
  fn Z = Into Z
  fn (S (m', r)) = Into $ S m'

-- debug functions
fromInt :: Int -> Nat
fromInt x
  | x > 0     = Into (S (fromInt (x - 1)))
  | otherwise = Into Z

-- could've been done with primitive recursion, but
-- to make sure it is correct, I've not done it
toInt :: Nat -> Int
toInt (Into n) = 
  case n of
    Z -> 0
    S n' -> 1 + toInt n'

data ListF a f = Nil | Cons a f deriving (Functor, Show)
type List a = Fix (ListF a)

fmapList :: (a -> b) -> List a -> List b
fmapList f = primRec fn where 
  -- fn x = Into (fmap (\(y1,y2) -> _) x)
  fn x = case x of 
    Nil -> nil
    Cons x (xs, r) -> cons (f x) r

instance Show a => Show (List a) where
  show xs = "[" ++ primRec fn xs ++ "]" where
    fn Nil = ""
    fn (Cons x (xs', r)) = show x ++ "," ++ r

nil :: List a
nil = Into Nil

cons :: a -> List a -> List a
cons x xs = Into (Cons x xs)

sing :: a -> List a
sing x = Into (Cons x (Into Nil))


rank :: forall a b. b -> a -> Int
rank _ _ = 0

data TreeF a f = Leaf a | Br f f deriving (Functor, Show)
type Tree a = Fix (TreeF a)

instance Show a => Show (Tree a) where
  show (Into tf) = show tf

z = Into Z
s = Into . S
leaf = Into . Leaf
br x y = Into (Br x y)

ofHeight :: Nat -> Tree Nat
ofHeight n = fst $ primRec fn n z where
  fn Z m           = (leaf m, s m)
  fn (S (m', r)) m = 
    let (t1, x) = r m
        (t2, y) = r x
    in (br t1 t2, y)

data SPF i o f
  = Get (i -> f)
  | Put o f

type SP i o = Fix (SPF i o)

idsp :: SP i i 
idsp = fix (\f -> Into $ Get (\x -> Into (Put x f)))
  

data A = A deriving (Show, Eq)
data B = B deriving (Show, Eq)

gen :: Bool -> Either A B
gen b = 
  case (\b' x -> x) :: Bool -> forall a. a -> a of 
    f -> case f b b of
        True -> Left (f b A)
        False -> Right (f b B)

data Fun a = Fun (forall b. (a,b))

instance Functor Fun where
  fmap f (Fun x1) = Fun (f (fst x1), snd x1)

tst :: forall a. (Int, a)
tst = let x :: forall b. (Int, b)
          x = undefined
      in  case x of (x1,x2) -> (x1,x2)
  
data MoreList a = MoreList a (List a) deriving Show

instance Functor MoreList where
  fmap f (MoreList x xs) = MoreList (f x) (fmapList f xs)

tst2 :: MoreList B
tst2 = 
  let as = MoreList A (cons A (cons A nil))
  in  fmap (const B) as

-- fun1 :: Fun Int
-- fun1 = Fun (0, [])

fib1 :: Int -> Int
fib1 n 
  | n <= 1 = n
  | otherwise = fib1 (n-1) + fib1 (n-2)

fib2 :: Int -> Int
fib2 = fixd (\f n -> if n <= 1 then n else f () (n-1) + f () (n-2))

fixd :: ((() -> a) -> a) -> a
fixd f =
  let x = f (\_ -> x)
  in  x

everyOther :: [a] -> [a]
everyOther [] = []
everyOther (x1:x2:xs) = x1 : everyOther xs

maap :: (a -> b) -> [a] -> [b]
maap f (x1 : x2 : xs) = f x1 : f x2 : maap f xs

badnats :: [Int]
badnats = 0 : maap (+1) badnats