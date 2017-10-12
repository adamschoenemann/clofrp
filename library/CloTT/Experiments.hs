{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}


module CloTT.Experiments where
-- This is just to keep some experiments around

-- Primitive recursion encoded with functors

-- F[μX. F[X]] -> (μX. F[X])
data Fix f = Into (f (Fix f))

-- (μX. F[X]) -> F[μX. F[X]]
out :: Fix f -> f (Fix f)
out (Into f) = f

data NatF a = Z | S a deriving Functor

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

data ListF a f = Nil | Cons a f
type List a = Fix (ListF a)

sing :: a -> List a
sing x = Into (Cons x (Into Nil))